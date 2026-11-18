/**
 * Haskell name resolution through the module system.
 *
 * A Haskell name means a definition of the module it is written in or of a
 * module that module imports — nothing else. `f` is one of the file's own
 * top-level definitions or comes from an unqualified import; `Q.f` comes from
 * an import whose `as` alias (or, without one, whose module name) is `Q`,
 * qualified or not. An import list (`import M (f, T(..))`) admits only what it
 * names, `hiding (…)` everything else. A module re-exports what its export
 * list says: `module Y` entries (the imports in scope as `Y`) and names it
 * imports and lists itself (`module P (f) where import Q (f)`).
 *
 * A name no visible module defines — Prelude/base, an external package, a
 * class method without a default — stays unresolved: binding it to a
 * same-named definition in an unrelated module is a wrong edge, and a wrong
 * edge is worse than none. Instance methods are never targets: a call to a
 * class method reaches whichever instance the type selects.
 *
 * A reader, not a parser: comments are blanked, then the module header and
 * each `import` declaration are read from their keywords.
 */

import type { Node, NodeKind } from '../types';
import type { ResolutionContext, ResolvedRef, UnresolvedRef } from './types';

/** What a reference of each kind may resolve to. */
const TARGET_KINDS: Partial<Record<UnresolvedRef['referenceKind'], ReadonlySet<NodeKind>>> = {
  calls: new Set<NodeKind>(['function', 'field']),
  function_ref: new Set<NodeKind>(['function', 'field']),
  instantiates: new Set<NodeKind>(['enum_member']),
  // The constructors a pattern matches (the Haskell extractor's only `references`).
  references: new Set<NodeKind>(['enum_member']),
};

/** Kinds that own children an import list can admit with `T(..)`. */
const CONTAINER_KINDS: ReadonlySet<NodeKind> = new Set<NodeKind>(['trait', 'struct']);

/** Names an import or export list mentions. */
interface NameList {
  /** Every name listed, a type's or class's listed children included. */
  names: Set<string>;
  /** Types/classes listed with all their children: `T(..)`. */
  allOf: Set<string>;
  /** `module Y` entries (export lists only). */
  modules: Set<string>;
}

interface HsImport {
  module: string;
  qualified: boolean;
  /** `as` alias, or null. */
  alias: string | null;
  hiding: boolean;
  /** The import list, or null for an import of everything. */
  list: NameList | null;
}

interface HsModule {
  /** The header's module name; null without a header (an implicit `Main`). */
  name: string | null;
  /** The header's export list; null exports every own definition and nothing else. */
  exports: NameList | null;
  imports: HsImport[];
}

/** A definition visible at module scope, with the type or class that owns it (`T` for a constructor or field). */
interface HsDef {
  node: Node;
  parent: string | null;
}

interface Memos {
  modules: Map<string, HsModule>;
  defs: Map<string, Map<string, HsDef[]>>;
  moduleFiles: Map<string, string[]>;
  /** exportedBy answers, per target-kind set, keyed `module\0name`. */
  exports: Map<ReadonlySet<NodeKind>, Map<string, HsDef[]>>;
}

const MEMOS = new WeakMap<ResolutionContext, Memos>();

function memosOf(context: ResolutionContext): Memos {
  let memos = MEMOS.get(context);
  if (!memos) {
    memos = { modules: new Map(), defs: new Map(), moduleFiles: new Map(), exports: new Map() };
    MEMOS.set(context, memos);
  }
  return memos;
}

/** Drops this module's per-context memos (the resolver clears them between runs). */
export function clearHaskellScopeMemos(context: ResolutionContext): void {
  MEMOS.delete(context);
}

const SYMBOL_CHARS = '!#$%&*+./<=>?@\\^|-~:';

/** `src` with `{- … -}` (nested) and `--` comments blanked, offsets and newlines kept. */
function blankComments(src: string): string {
  const blank = (text: string): string => text.replace(/[^\n]/g, ' ');
  const parts: string[] = [];
  let from = 0;
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === '"') {
      i++;
      while (i < src.length && src[i] !== '"' && src[i] !== '\n') i += src[i] === '\\' ? 2 : 1;
      i++;
      continue;
    }
    if (c === '\'') {
      // A character literal, not a prime in a name (`x'`).
      if (i > 0 && /[\w']/.test(src[i - 1]!)) {
        i++;
      } else if (src[i + 1] === '\\') {
        const close = src.indexOf('\'', i + 2);
        i = close < 0 ? i + 1 : close + 1;
      } else {
        i += src[i + 2] === '\'' ? 3 : 1;
      }
      continue;
    }
    if (c === '{' && src[i + 1] === '-') {
      let depth = 1;
      let j = i + 2;
      while (j < src.length && depth > 0) {
        if (src[j] === '{' && src[j + 1] === '-') { depth++; j += 2; }
        else if (src[j] === '-' && src[j + 1] === '}') { depth--; j += 2; }
        else j++;
      }
      parts.push(src.slice(from, i), blank(src.slice(i, j)));
      i = from = j;
      continue;
    }
    if (c === '-' && src[i + 1] === '-' && (i === 0 || !SYMBOL_CHARS.includes(src[i - 1]!))) {
      let j = i;
      while (src[j] === '-') j++;
      if (j >= src.length || !SYMBOL_CHARS.includes(src[j]!)) {
        const end = src.indexOf('\n', j);
        const stop = end < 0 ? src.length : end;
        parts.push(src.slice(from, i), blank(src.slice(i, stop)));
        i = from = stop;
        continue;
      }
      i = j;
      continue;
    }
    i++;
  }
  parts.push(src.slice(from));
  return parts.join('');
}

/** The index of the `)` closing the `(` at `open`, or the text's end. */
function closingParen(text: string, open: number): number {
  let depth = 0;
  for (let i = open; i < text.length; i++) {
    if (text[i] === '(') depth++;
    else if (text[i] === ')' && --depth === 0) return i;
  }
  return text.length;
}

/** Split a list's contents at its top-level commas. */
function splitTopLevel(text: string): string[] {
  const items: string[] = [];
  let depth = 0;
  let from = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '(') depth++;
    else if (text[i] === ')') depth--;
    else if (text[i] === ',' && depth === 0) {
      items.push(text.slice(from, i));
      from = i + 1;
    }
  }
  items.push(text.slice(from));
  return items.map((s) => s.trim()).filter((s) => s.length > 0);
}

/** `(<+>)` → `<+>`, `Q.f` → `f`, `f` → `f`. */
function listedName(item: string): string {
  const bare = item.startsWith('(') && item.endsWith(')') ? item.slice(1, -1).trim() : item;
  return bare.replace(/^(?:[A-Z][\w']*\.)+(?=[^.])/, '');
}

const LIST_ITEM = /^(\([^)]*\)|[\w'.]+)\s*(?:\(([\s\S]*)\))?$/;

function parseNameList(inner: string): NameList {
  const list: NameList = { names: new Set(), allOf: new Set(), modules: new Set() };
  for (const raw of splitTopLevel(inner)) {
    const moduleEntry = /^module\s+([A-Z][\w'.]*)$/.exec(raw);
    if (moduleEntry) {
      list.modules.add(moduleEntry[1]!);
      continue;
    }
    const item = LIST_ITEM.exec(raw.replace(/^(?:type|pattern)\s+/, ''));
    if (!item) continue;
    const base = listedName(item[1]!);
    list.names.add(base);
    if (item[2] === undefined) continue;
    for (const child of splitTopLevel(item[2])) {
      if (child === '..') list.allOf.add(base);
      else list.names.add(listedName(child));
    }
  }
  return list;
}

const MODULE_ID = "[A-Z][\\w']*(?:\\.[A-Z][\\w']*)*";

function parseImport(text: string, at: number): HsImport | null {
  let pos = at;
  const take = (re: RegExp): RegExpExecArray | null => {
    re.lastIndex = pos;
    const m = re.exec(text);
    if (m) pos = re.lastIndex;
    return m;
  };
  let qualified = false;
  for (let m = take(/\s*(?:(safe|qualified)\b|"(?:[^"\\\n]|\\.)*")/y); m; m = take(/\s*(?:(safe|qualified)\b|"(?:[^"\\\n]|\\.)*")/y)) {
    if (m[1] === 'qualified') qualified = true;
  }
  const mod = take(new RegExp(`\\s*(${MODULE_ID})`, 'y'));
  if (!mod) return null;
  if (take(/\s*qualified\b/y)) qualified = true;
  const alias = take(new RegExp(`\\s*as\\s+(${MODULE_ID})`, 'y'));
  const hiding = take(/\s*hiding\b/y) !== null;
  let list: NameList | null = null;
  if (take(/\s*\(/y)) {
    const open = pos - 1;
    list = parseNameList(text.slice(open + 1, closingParen(text, open)));
  }
  return { module: mod[1]!, qualified, alias: alias ? alias[1]! : null, hiding, list };
}

function parseModule(source: string): HsModule {
  const text = blankComments(source);
  const result: HsModule = { name: null, exports: null, imports: [] };
  const header = new RegExp(`(?:^|\\n)module\\s+(${MODULE_ID})\\s*`, 'g').exec(text);
  if (header) {
    result.name = header[1]!;
    const after = header.index + header[0].length;
    if (text[after] === '(') result.exports = parseNameList(text.slice(after + 1, closingParen(text, after)));
  }
  const importAt = /(?:^|\n)[ \t]*import\b/g;
  for (let m = importAt.exec(text); m; m = importAt.exec(text)) {
    const imp = parseImport(text, m.index + m[0].length);
    if (imp) result.imports.push(imp);
  }
  return result;
}

function moduleOf(filePath: string, context: ResolutionContext): HsModule {
  const memos = memosOf(context);
  let mod = memos.modules.get(filePath);
  if (!mod) {
    const source = context.readFile(filePath);
    mod = source ? parseModule(source) : { name: null, exports: null, imports: [] };
    memos.modules.set(filePath, mod);
  }
  return mod;
}

/** The project files declaring module `name`. */
function filesOfModule(name: string, context: ResolutionContext): string[] {
  const memos = memosOf(context);
  let files = memos.moduleFiles.get(name);
  if (!files) {
    files = context.getNodesByQualifiedName(name)
      .filter((n) => n.kind === 'namespace' && n.language === 'haskell')
      .map((n) => n.filePath);
    memos.moduleFiles.set(name, files);
  }
  return files;
}

/** A file's definitions visible at module scope, by name: top-level ones and the children of its types and classes. */
function defsOf(filePath: string, context: ResolutionContext): Map<string, HsDef[]> {
  const memos = memosOf(context);
  let defs = memos.defs.get(filePath);
  if (defs) return defs;
  defs = new Map();
  memos.defs.set(filePath, defs);
  const nodes = context.getNodesInFile(filePath).filter((n) => n.language === 'haskell');
  const ns = nodes.find((n) => n.kind === 'namespace');
  const prefix = ns ? `${ns.qualifiedName}::` : '';
  const containers = new Set(
    nodes.filter((n) => CONTAINER_KINDS.has(n.kind) && n.qualifiedName === prefix + n.name).map((n) => n.name),
  );
  for (const node of nodes) {
    if (node.kind === 'namespace' || node.kind === 'import' || node.kind === 'file') continue;
    if (!node.qualifiedName.startsWith(prefix)) continue;
    const rest = node.qualifiedName.slice(prefix.length);
    let parent: string | null;
    if (rest === node.name) {
      parent = null;
    } else if (node.kind === 'enum_member' || node.kind === 'field') {
      // Constructors and fields are module-scope names wherever they are
      // declared, a class instance's `data` family instance included
      // (`ESField.UserId::ESFieldValue::MkUserId`); their type owns them.
      const segments = rest.split('::');
      parent = segments[segments.length - 2] ?? null;
    } else {
      // `Class::defaultMethod` — never an instance's method (`Show.T::show`)
      // or a nested binding.
      const owner = rest.slice(0, rest.length - node.name.length - 2);
      if (!rest.endsWith(`::${node.name}`) || !containers.has(owner)) continue;
      parent = owner;
    }
    let named = defs.get(node.name);
    if (!named) defs.set(node.name, (named = []));
    named.push({ node, parent });
  }
  return defs;
}

function listAdmits(list: NameList, def: HsDef): boolean {
  return list.names.has(def.node.name) || (def.parent !== null && list.allOf.has(def.parent));
}

function importAdmits(imp: HsImport, def: HsDef): boolean {
  if (!imp.list) return true;
  return imp.hiding ? !listAdmits(imp.list, def) : listAdmits(imp.list, def);
}

/**
 * What module `moduleName` exports under `name`: its own definitions, or what
 * it re-exports. Memoized per (kinds, module, name); an entry being computed
 * reads as empty, which ends an import cycle.
 */
function exportedBy(moduleName: string, name: string, kinds: ReadonlySet<NodeKind>, context: ResolutionContext): HsDef[] {
  const memos = memosOf(context);
  let byKinds = memos.exports.get(kinds);
  if (!byKinds) memos.exports.set(kinds, (byKinds = new Map()));
  const key = `${moduleName}\0${name}`;
  const memo = byKinds.get(key);
  if (memo) return memo;
  byKinds.set(key, []);
  const out: HsDef[] = [];
  for (const file of filesOfModule(moduleName, context)) {
    const own = (defsOf(file, context).get(name) ?? []).filter((d) => kinds.has(d.node.kind));
    if (own.length > 0) {
      out.push(...own);
      continue;
    }
    const mod = moduleOf(file, context);
    const exports = mod.exports;
    if (!exports) continue;
    // `module Y`: everything in scope both unqualified and as `Y.`.
    for (const imp of mod.imports) {
      if (imp.qualified || !exports.modules.has(imp.alias ?? imp.module)) continue;
      for (const def of exportedBy(imp.module, name, kinds, context)) {
        if (importAdmits(imp, def)) out.push(def);
      }
    }
    // A name the module imports and lists itself.
    if (exports.names.has(name) || exports.allOf.size > 0) {
      for (const def of inScope(file, null, name, kinds, context)) {
        if (listAdmits(exports, def)) out.push(def);
      }
    }
  }
  byKinds.set(key, out);
  return out;
}

/** What `qualifier.name` (or bare `name`) means in `filePath`. */
function inScope(
  filePath: string,
  qualifier: string | null,
  name: string,
  kinds: ReadonlySet<NodeKind>,
  context: ResolutionContext,
): HsDef[] {
  const mod = moduleOf(filePath, context);
  if (qualifier === null || qualifier === mod.name) {
    const own = (defsOf(filePath, context).get(name) ?? []).filter((d) => kinds.has(d.node.kind));
    if (own.length > 0) return own;
  }
  const out: HsDef[] = [];
  for (const imp of mod.imports) {
    if (qualifier === null ? imp.qualified : (imp.alias ?? imp.module) !== qualifier) continue;
    for (const def of exportedBy(imp.module, name, kinds, context)) {
      if (importAdmits(imp, def)) out.push(def);
    }
  }
  return out;
}

function commonPrefixLength(a: string, b: string): number {
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i++;
  return i;
}

/**
 * Resolve a Haskell call, value, constructor or class reference through the
 * module system: the definition it names, or null when no module in scope
 * defines it. Undefined for other languages and reference kinds.
 */
export function resolveHaskellRef(ref: UnresolvedRef, context: ResolutionContext): ResolvedRef | null | undefined {
  if (ref.language !== 'haskell') return undefined;
  const kinds = TARGET_KINDS[ref.referenceKind];
  if (!kinds) return undefined;
  const qualified = /^((?:[A-Z][\w']*\.)*[A-Z][\w']*)\.(.+)$/.exec(ref.referenceName);
  const qualifier = qualified ? qualified[1]! : null;
  const name = qualified ? qualified[2]! : ref.referenceName;
  const defs = inScope(ref.filePath, qualifier, name, kinds, context);
  if (defs.length === 0) return null;
  // Two modules of one name (two packages of a monorepo): the one nearest the caller.
  let best = defs[0]!.node;
  let bestScore = -1;
  for (const { node } of defs) {
    const score = node.filePath === ref.filePath ? Infinity : commonPrefixLength(node.filePath, ref.filePath);
    if (score > bestScore) {
      best = node;
      bestScore = score;
    }
  }
  return {
    original: ref,
    targetNodeId: best.id,
    confidence: best.filePath === ref.filePath ? 0.95 : 0.9,
    resolvedBy: qualifier ? 'qualified-name' : 'import',
  };
}
