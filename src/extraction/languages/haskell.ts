import type { Node as SyntaxNode } from 'web-tree-sitter';
import { getNodeText, getChildByField } from '../tree-sitter-helpers';
import type { LanguageExtractor, ExtractorContext } from '../tree-sitter-types';

// Node names follow the tree-sitter-haskell grammar 0.23.1 (vendored, ABI 14).
//
// Haskell's AST shapes don't map to the generic extractor's bodyField-based
// dispatch — different node kinds use different field names for their body
// (`match` for functions, `declarations` for class/instance bodies, no field
// for data-type constructors). Every symbol-bearing top-level declaration is
// dispatched through the visitNode hook below, mirroring the Erlang
// extractor's approach.
//
// Calls live entirely here. Each top-level clause's body is walked by
// visitBodyNode (the hook takes over every node under a body), which skips
// pattern and type positions and records, against the enclosing top-level
// function:
//   - `calls` for an applied name: the head of an application (`f x`, `Q.f x`),
//     a do-statement or bind right-hand side (`y <- act`, `act`), the left
//     operand of `$` and the right operand of `&`, and non-builtin operators;
//   - `function_ref` for a name used as a value — an argument (`map f xs`),
//     an operand (`f . g`, `f <$> m`), a list/tuple element — the
//     function-as-value convention (#756), which persists as `references`;
//   - `instantiates` for data constructors, `references` for the constructors
//     a pattern matches (`Just v -> …`).
// let/where bindings are not symbols of their own: their calls belong to the
// enclosing top-level function, and names a clause binds locally (parameters,
// pattern variables, let/where names) are never recorded as references.
// Which definition a name means is decided by the import-aware Haskell
// resolver (src/resolution/haskell-scope.ts).

/** Collapse runs of whitespace for one-line signatures. */
function collapseWs(text: string): string {
  return text.replace(/\s+/g, ' ').trim();
}

/** Read the text of a `module` node as a dotted module name (`Data.List`). */
function moduleDottedName(node: SyntaxNode, source: string): string {
  const parts: string[] = [];
  for (let i = 0; i < node.namedChildCount; i++) {
    const child = node.namedChild(i);
    if (child?.type === 'module_id') {
      parts.push(getNodeText(child, source));
    }
  }
  return parts.join('.');
}

/** Extract a Haddock comment (`-- | ...` / `{- | ... -}`) preceding a node.
 *  Haddocks sit as siblings of the `declarations` container (not as siblings
 *  of the declaration itself), so climb out of `declarations` to find them. */
function precedingHaddock(node: SyntaxNode, source: string): string | undefined {
  // Climb out of `declarations` so we see top-level siblings (haddocks sit
  // alongside `declarations`, not inside it).
  let anchor: SyntaxNode = node;
  while (anchor.parent && anchor.parent.type === 'declarations') anchor = anchor.parent;
  let sibling = anchor.previousNamedSibling;
  while (sibling?.type === 'haddock' || sibling?.type === 'comment') {
    if (sibling.type === 'haddock') {
      const text = getNodeText(sibling, source)
        .replace(/^--\s*\|?\s*/, '')
        .replace(/^\{-\s*\|?\s*/, '')
        .replace(/-}$/, '')
        .trim();
      return text || undefined;
    }
    sibling = sibling.previousNamedSibling;
  }
  return undefined;
}

/** The name a binding-name node spells: `f`, or `<+>` for `(<+>)`. */
function bindingName(nameNode: SyntaxNode, source: string): string {
  if (nameNode.type === 'prefix_id') {
    const op = nameNode.namedChild(0);
    return op ? getNodeText(op, source) : '';
  }
  return getNodeText(nameNode, source);
}

/** A definition's unlabeled `infix` head — `a <+> b = …`, ``x `op` y = …``. */
function infixHead(node: SyntaxNode): SyntaxNode | null {
  for (let i = 0; i < node.childCount; i++) {
    const child = node.child(i);
    if (child?.type === 'infix' && node.fieldNameForChild(i) === null) return child;
  }
  return null;
}

/** The name a `function`/`bind` defines: its `name` field, or an infix definition's operator. */
function definedName(node: SyntaxNode, source: string): string | null {
  const nameNode = getChildByField(node, 'name');
  if (nameNode) return bindingName(nameNode, source) || null;
  const head = infixHead(node);
  const op = head ? getChildByField(head, 'operator') : null;
  if (!op) return null;
  if (op.type === 'infix_id') {
    const inner = op.namedChild(0);
    return inner ? getNodeText(inner, source) : null;
  }
  return getNodeText(op, source) || null;
}

/** The preceding `signature` sibling (comments/haddocks may sit between), if it names this function. */
function precedingSignature(node: SyntaxNode, name: string, source: string): SyntaxNode | null {
  let prev = node.previousNamedSibling;
  while (prev && (prev.type === 'comment' || prev.type === 'haddock')) prev = prev.previousNamedSibling;
  if (prev?.type === 'signature') {
    const sigName = getChildByField(prev, 'name');
    if (sigName && bindingName(sigName, source) === name) return prev;
  }
  return null;
}

// --- Per-file memos. Extraction is file-sequential within a worker, so a
// single-entry memo keyed by filePath is safe (and resets naturally). ---

/** Clause-merge state: consecutive same-name function/bind nodes *in the same
 * enclosing scope* merge into one. The scope key is the top of the node stack
 * (the instance/class/top-level container) so two `instance` blocks each
 * defining `show` don't collapse into one node. */
let lastFnFile = '';
let lastFnName = '';
let lastFnScope = '';
let lastFnId = '';

function resetFnMemo(filePath: string): void {
  if (lastFnFile !== filePath) {
    lastFnFile = filePath;
    lastFnName = '';
    lastFnScope = '';
    lastFnId = '';
  }
}

// --- Calls and value references inside function bodies. ---

/**
 * Infix operators that are always built-in (never a user-defined function),
 * so a call edge would never resolve. User-defined operators are NOT in this
 * set and DO get a call edge.
 */
const BUILTIN_OPS = new Set([
  '+', '-', '*', '/', '^', '^^', '**',
  '==', '/=', '<', '>', '<=', '>=',
  '&&', '||', 'not',
  '>>', '>>=', '<<', '<$>', '<*>', '<|', '|$', '$', '$!',
  '.', '..', '++', '!!', ':',
  '<>', '<$',
]);

/** Operators whose left operand is the function applied: `f $ x`. */
const APPLIES_LEFT = new Set(['$', '$!']);
/** Operators whose right operand is the function applied: `x & f`. */
const APPLIES_RIGHT = new Set(['&']);

/** Body nodes holding no references: type positions, raw quasiquote text, record field labels. */
const SKIPPED_BODY_NODES = new Set(['type_application', 'quasiquote', 'pragma', 'comment', 'haddock', 'field_name']);

/** Depth of top-level clause bodies being walked; > 0 routes the hook to visitBodyNode. */
let bodyDepth = 0;
/** Names the clause being walked binds locally (parameters, pattern variables, let/where names). */
let bodyLocals: Set<string> | null = null;
/** `function_ref`/`references` dedupe — one per (caller, name), as flushFnRefCandidates does. */
let refFile = '';
let refSeen = new Set<string>();

/** Every name a top-level clause binds below its own name: what its body's names may mean locally. */
function collectLocals(clause: SyntaxNode, source: string): Set<string> {
  const locals = new Set<string>();
  const addVariables = (node: SyntaxNode): void => {
    if (node.type === 'variable') locals.add(getNodeText(node, source));
    for (let i = 0; i < node.namedChildCount; i++) {
      const child = node.namedChild(i);
      if (child) addVariables(child);
    }
  };
  const scan = (node: SyntaxNode, top: boolean): void => {
    const isDefinition = node.type === 'function' || node.type === 'bind';
    for (let i = 0; i < node.childCount; i++) {
      const child = node.child(i);
      if (!child?.isNamed) continue;
      const field = node.fieldNameForChild(i);
      if (field === 'pattern' || field === 'patterns') {
        addVariables(child);
      } else if (isDefinition && field === 'name') {
        if (!top) locals.add(bindingName(child, source));
      } else if (isDefinition && field === null && child.type === 'infix') {
        // `a <+> b = …`: the operands are the parameters.
        for (const operand of [getChildByField(child, 'left_operand'), getChildByField(child, 'right_operand')]) {
          if (operand) addVariables(operand);
        }
        const name = top ? null : definedName(node, source);
        if (name) locals.add(name);
      } else {
        scan(child, false);
      }
    }
  };
  scan(clause, true);
  return locals;
}

type RefKind = 'calls' | 'function_ref' | 'instantiates' | 'references';

/** Record a reference from the enclosing symbol, unless it names a builtin operator or a local. */
function emitRef(ctx: ExtractorContext, name: string, kind: RefKind, at: SyntaxNode): void {
  const fromNodeId = ctx.nodeStack[ctx.nodeStack.length - 1];
  if (!fromNodeId || !name || BUILTIN_OPS.has(name)) return;
  if ((kind === 'calls' || kind === 'function_ref') && bodyLocals?.has(name)) return;
  if (kind === 'function_ref' || kind === 'references') {
    if (refFile !== ctx.filePath) {
      refFile = ctx.filePath;
      refSeen = new Set();
    }
    const key = `${kind}|${fromNodeId}|${name}`;
    if (refSeen.has(key)) return;
    refSeen.add(key);
  }
  ctx.addUnresolvedReference({
    fromNodeId,
    referenceName: name,
    referenceKind: kind,
    line: at.startPosition.row + 1,
    column: at.startPosition.column,
  });
}

/** A bare name expression — `f`, `M.f`, `Just`, `M.Just`, `(<+>)`, an operator — and whether it is a data constructor. */
function bareName(node: SyntaxNode, source: string): { name: string; ctor: boolean } | null {
  switch (node.type) {
    case 'variable':
    case 'operator':
      return { name: getNodeText(node, source), ctor: false };
    case 'constructor':
    case 'constructor_operator':
      return { name: getNodeText(node, source), ctor: true };
    case 'qualified': {
      const id = getChildByField(node, 'id');
      if (!id) return null;
      return { name: getNodeText(node, source), ctor: id.type === 'constructor' || id.type === 'constructor_operator' };
    }
    case 'prefix_id':
    case 'infix_id': {
      const inner = node.namedChild(0);
      return inner ? bareName(inner, source) : null;
    }
    default:
      return null;
  }
}

/** Record `node` as a reference of `kind` if it is a bare name; otherwise walk it. */
function visitOperand(ctx: ExtractorContext, node: SyntaxNode, kind: 'calls' | 'function_ref'): void {
  const ref = bareName(node, ctx.source);
  if (ref) emitRef(ctx, ref.name, ref.ctor ? 'instantiates' : kind, node);
  else ctx.visitNode(node);
}

/** An operator in an infix expression or section is applied: a call (constructor operators instantiate). */
function visitOperator(ctx: ExtractorContext, op: SyntaxNode): string {
  const ref = bareName(op, ctx.source);
  if (!ref) return '';
  emitRef(ctx, ref.name, ref.ctor ? 'instantiates' : 'calls', op);
  return ref.name;
}

/** A pattern binds names; the constructors it matches are `references` (`Just v -> …`). */
function visitPattern(ctx: ExtractorContext, node: SyntaxNode): void {
  const ref = bareName(node, ctx.source);
  if (ref) {
    if (ref.ctor) emitRef(ctx, ref.name, 'references', node);
    return;
  }
  for (let i = 0; i < node.namedChildCount; i++) {
    const child = node.namedChild(i);
    if (child) visitPattern(ctx, child);
  }
}

/**
 * A definition (`function`/`bind`) or do-statement bind, as code of the
 * enclosing top-level function: patterns (an infix definition's operands
 * included) for the constructors they match, then guards, right-hand sides and
 * `where` binds. Its name is never a reference.
 */
function visitBinding(node: SyntaxNode, ctx: ExtractorContext): void {
  for (let i = 0; i < node.childCount; i++) {
    const child = node.child(i);
    if (!child?.isNamed) continue;
    const field = node.fieldNameForChild(i);
    if (field === 'expression') visitOperand(ctx, child, 'calls');
    else if (field === 'match' || field === 'binds') ctx.visitNode(child);
    else if (field === 'pattern' || field === 'patterns') visitPattern(ctx, child);
    else if (field === null && child.type === 'infix') {
      for (const operand of [getChildByField(child, 'left_operand'), getChildByField(child, 'right_operand')]) {
        if (operand) visitPattern(ctx, operand);
      }
    }
  }
}

/** The hook while a top-level clause body is walked: every node under it comes here. */
function visitBodyNode(node: SyntaxNode, ctx: ExtractorContext): boolean {
  switch (node.type) {
    case 'function':
    case 'bind':
      // A let/where binding or a do-statement `x <- act`, never a symbol of its
      // own: its right-hand side belongs to the enclosing top-level function.
      visitBinding(node, ctx);
      return true;
    case 'exp':
      // A do-statement: a bare action is run.
      for (let i = 0; i < node.namedChildCount; i++) {
        const child = node.namedChild(i);
        if (child) visitOperand(ctx, child, 'calls');
      }
      return true;
    case 'apply': {
      // `f a b` nests as apply(apply(f, a), b): the innermost apply names the head.
      const fn = getChildByField(node, 'function');
      if (fn) visitOperand(ctx, fn, 'calls');
      for (const arg of node.childrenForFieldName('argument')) {
        if (arg) visitOperand(ctx, arg, 'function_ref');
      }
      return true;
    }
    case 'infix': {
      const op = getChildByField(node, 'operator');
      const opName = op ? visitOperator(ctx, op) : '';
      const left = getChildByField(node, 'left_operand');
      const right = getChildByField(node, 'right_operand');
      if (left) visitOperand(ctx, left, APPLIES_LEFT.has(opName) ? 'calls' : 'function_ref');
      if (right) visitOperand(ctx, right, APPLIES_RIGHT.has(opName) ? 'calls' : 'function_ref');
      return true;
    }
    case 'left_section':
    case 'right_section': {
      // `(f <$>)`, ``(`elem` xs)``, `(+ 1)`: the operator is applied, operands are values.
      let opName = '';
      const operands: Array<[SyntaxNode, string]> = [];
      for (let i = 0; i < node.childCount; i++) {
        const child = node.child(i);
        if (!child?.isNamed) continue;
        const field = node.fieldNameForChild(i);
        if (field === 'left_operand' || field === 'right_operand') operands.push([child, field]);
        else if (field === 'operator' || child.type === 'operator' || child.type === 'infix_id' || child.type === 'constructor_operator') {
          opName = visitOperator(ctx, child);
        } else ctx.visitNode(child);
      }
      for (const [operand, field] of operands) {
        const applied = field === 'left_operand' ? APPLIES_LEFT.has(opName) : APPLIES_RIGHT.has(opName);
        visitOperand(ctx, operand, applied ? 'calls' : 'function_ref');
      }
      return true;
    }
    case 'signature': {
      // `(e :: T)` walks `e`; a local type signature holds no references.
      const expr = getChildByField(node, 'expression');
      if (expr) visitOperand(ctx, expr, 'function_ref');
      return true;
    }
    case 'variable':
    case 'qualified':
    case 'constructor':
    case 'prefix_id':
      visitOperand(ctx, node, 'function_ref');
      return true;
    default:
      if (SKIPPED_BODY_NODES.has(node.type)) return true;
      for (let i = 0; i < node.childCount; i++) {
        const child = node.child(i);
        if (!child?.isNamed) continue;
        const field = node.fieldNameForChild(i);
        if (field === 'pattern' || field === 'patterns') visitPattern(ctx, child);
        else if (field !== 'type') ctx.visitNode(child);
      }
      return true;
  }
}

/** Walk one top-level clause (patterns, guards, body, `where` binds) as `fnId`'s code. */
function walkClause(node: SyntaxNode, fnId: string, ctx: ExtractorContext): void {
  const outerLocals = bodyLocals;
  bodyLocals = collectLocals(node, ctx.source);
  bodyDepth++;
  ctx.pushScope(fnId);
  try {
    visitBinding(node, ctx);
  } finally {
    ctx.popScope();
    bodyDepth--;
    bodyLocals = outerLocals;
  }
}

/** Handle a top-level (or class/instance member) `function` or `bind` node. */
function handleFunctionLike(node: SyntaxNode, ctx: ExtractorContext): boolean {
  const name = definedName(node, ctx.source);
  if (!name) return true;

  resetFnMemo(ctx.filePath);

  // Continuation clause: same-name consecutive function *in the same enclosing
  // scope* — extend the existing node and attribute this clause's calls to it.
  // The scope key (top of nodeStack) distinguishes methods of different
  // type-class instances that happen to share a name (e.g. two `show` impls).
  const currentScope = ctx.nodeStack[ctx.nodeStack.length - 1] ?? '';
  if (name === lastFnName && lastFnId && currentScope === lastFnScope) {
    for (let i = ctx.nodes.length - 1; i >= 0; i--) {
      const n = ctx.nodes[i];
      if (n && n.id === lastFnId) {
        if (node.endPosition.row + 1 > n.endLine) n.endLine = node.endPosition.row + 1;
        break;
      }
    }
    walkClause(node, lastFnId, ctx);
    return true;
  }

  const sig = precedingSignature(node, name, ctx.source);
  const doc = precedingHaddock(sig ?? node, ctx.source);
  const fn = ctx.createNode('function', name, node, {
    docstring: doc,
    signature: sig ? collapseWs(getNodeText(sig, ctx.source)).slice(0, 300) : undefined,
  });
  if (!fn) return true;
  lastFnName = name;
  lastFnScope = currentScope;
  lastFnId = fn.id;

  walkClause(node, fn.id, ctx);
  return true;
}

/** Handle a `data_type` node — struct + constructors (enum_members) + record fields.
 *  `name` overrides the struct's name (a data family instance's, see handleDataInstance). */
function handleDataType(node: SyntaxNode, ctx: ExtractorContext, name?: string): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  const doc = precedingHaddock(node, ctx.source);
  const struct = ctx.createNode('struct', name ?? getNodeText(nameNode, ctx.source), node, {
    docstring: doc,
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 300),
  });
  if (!struct) return true;

  ctx.pushScope(struct.id);
  const ctors = getChildByField(node, 'constructors');
  if (ctors) {
    for (let i = 0; i < ctors.namedChildCount; i++) {
      const dc = ctors.namedChild(i);
      if (!dc || dc.type !== 'data_constructor') continue;
      // The constructor shape is under a `prefix`, `record`, or `infix` child
      // (field `constructor`).
      const shape = getChildByField(dc, 'constructor');
      if (!shape) continue;
      const ctorNameNode = getChildByField(shape, 'name') || getChildByField(shape, 'constructor');
      const ctorName = ctorNameNode ? getNodeText(ctorNameNode, ctx.source) : null;
      if (ctorName) {
        ctx.createNode('enum_member', ctorName, dc);
      }
      // Record fields
      if (shape.type === 'record') {
        const fields = getChildByField(shape, 'fields');
        if (fields) {
          for (let j = 0; j < fields.namedChildCount; j++) {
            const field = fields.namedChild(j);
            if (!field || field.type !== 'field') continue;
            const fNameNode = getChildByField(field, 'name');
            if (fNameNode) ctx.createNode('field', getNodeText(fNameNode, ctx.source), field);
          }
        }
      }
    }
  }
  ctx.popScope();
  return true; // don't descend into type-position expressions
}

/** Handle a `newtype` node — struct + single constructor + field.
 *  `name` overrides the struct's name (a data family instance's, see handleDataInstance). */
function handleNewtype(node: SyntaxNode, ctx: ExtractorContext, name?: string): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  const struct = ctx.createNode('struct', name ?? getNodeText(nameNode, ctx.source), node, {
    docstring: precedingHaddock(node, ctx.source),
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 300),
  });
  if (!struct) return true;

  ctx.pushScope(struct.id);
  const ctor = getChildByField(node, 'constructor');
  if (ctor) {
    const ctorNameNode = getChildByField(ctor, 'name') || getChildByField(ctor, 'constructor');
    if (ctorNameNode) ctx.createNode('enum_member', getNodeText(ctorNameNode, ctx.source), ctor);
    const field = getChildByField(ctor, 'field');
    if (field) {
      const fNameNode = getChildByField(field, 'name');
      if (fNameNode) ctx.createNode('field', getNodeText(fNameNode, ctx.source), field);
    }
  }
  ctx.popScope();
  return true;
}

/** Handle a `type_synomym` node (note: grammar typo is intentional) — type_alias. */
function handleTypeSynonym(node: SyntaxNode, ctx: ExtractorContext): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  ctx.createNode('type_alias', getNodeText(nameNode, ctx.source), node, {
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 200),
  });
  return true; // the type body is type-position — don't descend
}

/**
 * Handle a `type_family` / `data_family` declaration, top-level or associated
 * (`type F a :: Type`, `data D a` in a class body). Indexed like the type
 * synonym / data type it stands for: `type_alias` and `struct`.
 */
function handleFamily(node: SyntaxNode, ctx: ExtractorContext, kind: 'type_alias' | 'struct'): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  ctx.createNode(kind, getNodeText(nameNode, ctx.source), node, {
    docstring: precedingHaddock(node, ctx.source),
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 200),
  });
  return true; // kind signature, equations: type positions — don't descend
}

/** `implements` from the enclosing symbol to the family a type/data instance instantiates. */
function referenceFamily(nameNode: SyntaxNode, node: SyntaxNode, ctx: ExtractorContext): void {
  const fromNodeId = ctx.nodeStack[ctx.nodeStack.length - 1];
  if (!fromNodeId) return;
  ctx.addUnresolvedReference({
    fromNodeId,
    referenceName: getNodeText(nameNode, ctx.source),
    referenceKind: 'implements',
    line: node.startPosition.row + 1,
    column: node.startPosition.column,
  });
}

/**
 * Handle a `type_instance` node (`type F Foo = …`, `type instance F Foo = …`):
 * a reference to the family, so its usages are reachable. A default in a class
 * body (`type F a = …`) restates the family declared there: nothing to link.
 */
function handleTypeInstance(node: SyntaxNode, ctx: ExtractorContext): boolean {
  if (node.parent?.type === 'class_declarations') return true;
  const nameNode = getChildByField(node, 'name');
  if (nameNode) referenceFamily(nameNode, node, ctx);
  return true;
}

/**
 * Handle a `data_instance` node (`data`/`newtype` `F Foo = …`, with or without
 * `instance`): a reference to the family, plus a struct for the instance with
 * its constructors and fields. The struct is named `Family.Patterns`, as an
 * instance's class node is (`Shape.Circle`): sharing the family's name, it
 * would be taken for the family itself.
 */
function handleDataInstance(node: SyntaxNode, ctx: ExtractorContext): boolean {
  const body = node.namedChildren.find((c) => c.type === 'data_type' || c.type === 'newtype');
  if (!body) return true;
  const nameNode = getChildByField(body, 'name');
  if (!nameNode) return true;
  referenceFamily(nameNode, node, ctx);
  const patterns = getChildByField(body, 'patterns');
  const family = getNodeText(nameNode, ctx.source);
  const name = patterns ? `${family}.${collapseWs(getNodeText(patterns, ctx.source))}` : family;
  return body.type === 'newtype' ? handleNewtype(body, ctx, name) : handleDataType(body, ctx, name);
}

/** Handle a `class` node — trait + default method implementations. */
function handleClass(node: SyntaxNode, ctx: ExtractorContext): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  const trait = ctx.createNode('trait', getNodeText(nameNode, ctx.source), node, {
    docstring: precedingHaddock(node, ctx.source),
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 300),
  });
  if (!trait) return true;

  ctx.pushScope(trait.id);
  const decls = getChildByField(node, 'declarations');
  if (decls) {
    for (let i = 0; i < decls.namedChildCount; i++) {
      const child = decls.namedChild(i);
      if (child) ctx.visitNode(child);
    }
  }
  ctx.popScope();
  return true;
}

/** Handle an `instance` node — class node + implements reference + methods. */
function handleInstance(node: SyntaxNode, ctx: ExtractorContext): boolean {
  const nameNode = getChildByField(node, 'name');
  if (!nameNode) return true;
  const className = getNodeText(nameNode, ctx.source);
  // Derive the instance type from `patterns: type_patterns`
  const typePatterns = getChildByField(node, 'patterns');
  let instanceType = '';
  if (typePatterns) {
    const firstChild = typePatterns.namedChild(0);
    if (firstChild) instanceType = getNodeText(firstChild, ctx.source);
  }
  const instanceName = instanceType ? `${className}.${instanceType}` : className;
  const parentId = ctx.nodeStack[ctx.nodeStack.length - 1];

  const instNode = ctx.createNode('class', instanceName, node, {
    signature: collapseWs(getNodeText(node, ctx.source)).slice(0, 300),
  });

  // Emit an `implements` reference to the class so the resolver links it.
  if (parentId) {
    ctx.addUnresolvedReference({
      fromNodeId: instNode?.id ?? parentId,
      referenceName: className,
      referenceKind: 'implements',
      line: node.startPosition.row + 1,
      column: node.startPosition.column,
    });
  }

  if (!instNode) return true;

  ctx.pushScope(instNode.id);
  const decls = getChildByField(node, 'declarations');
  if (decls) {
    for (let i = 0; i < decls.namedChildCount; i++) {
      const child = decls.namedChild(i);
      if (child) ctx.visitNode(child);
    }
  }
  ctx.popScope();
  return true;
}

export const haskellExtractor: LanguageExtractor = {
  functionTypes: [],  // dispatched via visitNode (name lives on a `variable` child of the `function`/`bind` node)
  classTypes: [],
  methodTypes: [],
  interfaceTypes: [],
  structTypes: [],     // dispatched via visitNode
  enumTypes: [],
  typeAliasTypes: [],  // dispatched via visitNode
  importTypes: ['import'],
  callTypes: [],  // calls are recorded by visitBodyNode (see the header comment)
  variableTypes: [],
  nameField: 'name',
  bodyField: 'match',
  paramsField: 'patterns',
  interfaceKind: 'trait',

  // `header` wraps `module: module` → wraps the file's declarations in a
  // namespace so qualified calls (`Data.Map.fromList`) resolve via
  // matchByQualifiedName — mirrors Erlang's -module(m).
  packageTypes: ['header'],
  extractPackage: (node, source) => {
    const mod = getChildByField(node, 'module');
    if (!mod) return null;
    return moduleDottedName(mod, source);
  },

  extractImport: (node, source) => {
    const modNode = getChildByField(node, 'module');
    if (!modNode) return null;
    const moduleName = moduleDottedName(modNode, source);
    if (!moduleName) return null;
    return {
      moduleName,
      signature: collapseWs(getNodeText(node, source)).slice(0, 200),
    };
  },

  visitNode: (node, ctx) => {
    if (bodyDepth > 0) return visitBodyNode(node, ctx);
    switch (node.type) {
      case 'function':
      case 'bind':
        return handleFunctionLike(node, ctx);
      case 'top_splice':
        // `makeLenses ''Foo` at the top level: the file's own code.
        bodyDepth++;
        try {
          for (let i = 0; i < node.namedChildCount; i++) {
            const child = node.namedChild(i);
            if (child) ctx.visitNode(child);
          }
        } finally {
          bodyDepth--;
        }
        return true;
      case 'signature':
        return true; // metadata for the following function — skip as a node
      case 'data_type':
        return handleDataType(node, ctx);
      case 'newtype':
        return handleNewtype(node, ctx);
      case 'type_synomym':
        return handleTypeSynonym(node, ctx);
      case 'type_family':
        return handleFamily(node, ctx, 'type_alias');
      case 'data_family':
        return handleFamily(node, ctx, 'struct');
      case 'type_instance':
        return handleTypeInstance(node, ctx);
      case 'data_instance':
        return handleDataInstance(node, ctx);
      case 'class':
        return handleClass(node, ctx);
      case 'instance':
        return handleInstance(node, ctx);
      case 'haddock':
      case 'comment':
        return true;
      default:
        return false;
    }
  },
};