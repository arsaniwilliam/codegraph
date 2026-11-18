import * as path from 'path';
import { Node, Edge, ExtractionResult, ExtractionError, UnresolvedReference } from '../types';
import { generateNodeId, NodeIdAllocator } from './tree-sitter-helpers';

/** The front-matter keys the file node carries; `bodyStart` is the 0-based first line after the block. */
interface FrontMatter {
  title?: string;
  description?: string;
  topics: string[];
  keySymbols: string[];
  dependsOn: Array<{ target: string; line: number }>;
  bodyStart: number;
}

/**
 * MarkdownExtractor - sections and cross-document links of `.md` files.
 *
 * - A file node whose docstring carries the front-matter `title`,
 *   `description` and `topics`, and whose signature carries `key-symbols`, so
 *   a search for a symbol or topic finds the doc that documents it.
 * - One `module` node per ATX heading outside fenced code. Its name is the
 *   heading text, its qualified name `<file>#<github-slug>`, and its span runs
 *   from the heading line to the line before the next heading of the same or
 *   higher level, so a section's source is its text verbatim. Every section is
 *   a direct child of the file (flat `contains`): a nested `contains` would make
 *   a parent section a container whose `codegraph_node` body is an outline.
 * - A `references` edge for every inline link to a `.md` target: `(#slug)` to
 *   the section of this file, `(path.md#slug)` to that section of the target,
 *   `(path.md)` to the target's file node. Front-matter `depends-on: - doc:`
 *   entries reference their file. The link's source is the innermost section
 *   it sits in (the file node above the first heading).
 *
 * Cross-file targets are written as project-relative `path.md` / `path.md#slug`
 * reference names, which the resolver looks up by qualified name
 * (`matchMarkdownReference`).
 */
export class MarkdownExtractor {
  private filePath: string;
  private lines: string[];
  private nodes: Node[] = [];
  private nodeIds = new NodeIdAllocator();
  private edges: Edge[] = [];
  private unresolvedReferences: UnresolvedReference[] = [];
  private errors: ExtractionError[] = [];

  constructor(filePath: string, source: string) {
    this.filePath = filePath;
    this.lines = source.split('\n');
  }

  extract(): ExtractionResult {
    const startTime = Date.now();
    try {
      const frontMatter = this.parseFrontMatter();
      const fileNode = this.createFileNode(frontMatter);
      for (const doc of frontMatter.dependsOn) {
        this.addLinkReference(fileNode.id, doc.target, doc.line, 0);
      }
      const sections = this.extractSections(fileNode.id, frontMatter.bodyStart);
      this.extractLinks(fileNode.id, sections, frontMatter.bodyStart);
    } catch (error) {
      this.errors.push({
        message: `Markdown extraction error: ${error instanceof Error ? error.message : String(error)}`,
        severity: 'error',
        code: 'parse_error',
      });
    }
    return {
      nodes: this.nodes,
      edges: this.edges,
      unresolvedReferences: this.unresolvedReferences,
      errors: this.errors,
      durationMs: Date.now() - startTime,
    };
  }

  /**
   * The leading `---` … `---` YAML block, read for the handful of keys the
   * file node carries. Only the flat shapes front matter is written in: a
   * scalar, an inline `[a, b]` list, a block `- a` list, and `depends-on`'s
   * `- doc: path` entries. `bodyStart` is the 0-based first line after it.
   */
  private parseFrontMatter(): FrontMatter {
    const result: FrontMatter = { topics: [], keySymbols: [], dependsOn: [], bodyStart: 0 };
    if (this.lines[0]?.trimEnd() !== '---') return result;
    let end = -1;
    for (let i = 1; i < this.lines.length; i++) {
      const l = this.lines[i]!.trimEnd();
      if (l === '---' || l === '...') { end = i; break; }
    }
    if (end < 0) return result;
    result.bodyStart = end + 1;

    let key: string | undefined;
    for (let i = 1; i < end; i++) {
      const raw = this.lines[i]!;
      const top = /^([A-Za-z0-9_-]+):\s*(.*)$/.exec(raw);
      if (top) {
        key = top[1]!;
        const value = top[2]!.trim();
        if (value === '') continue;
        if (key === 'title') result.title = unquote(value);
        else if (key === 'description') result.description = unquote(value);
        else if (key === 'topics') result.topics.push(...inlineList(value));
        else if (key === 'key-symbols') result.keySymbols.push(...inlineList(value));
        continue;
      }
      const item = /^\s+-\s+(.*)$/.exec(raw);
      if (!item || !key) continue;
      const value = item[1]!.trim();
      if (key === 'topics') result.topics.push(unquote(value));
      else if (key === 'key-symbols') result.keySymbols.push(unquote(value));
      else if (key === 'depends-on') {
        const doc = /^doc:\s*(.+)$/.exec(value);
        // KB `depends-on` doc paths are project-relative.
        if (doc) result.dependsOn.push({ target: '/' + unquote(doc[1]!.trim()), line: i + 1 });
      }
    }
    return result;
  }

  private createFileNode(fm: FrontMatter): Node {
    const docParts: string[] = [];
    if (fm.title) docParts.push(fm.title);
    if (fm.description) docParts.push(fm.description);
    if (fm.topics.length > 0) docParts.push(`Topics: ${fm.topics.join(', ')}`);
    const node: Node = {
      id: generateNodeId(this.filePath, 'file', this.filePath, 1),
      kind: 'file',
      name: this.filePath.split('/').pop() || this.filePath,
      qualifiedName: this.filePath,
      filePath: this.filePath,
      language: 'markdown',
      startLine: 1,
      endLine: this.lines.length,
      startColumn: 0,
      endColumn: this.lines[this.lines.length - 1]?.length || 0,
      docstring: docParts.length > 0 ? docParts.join('\n\n') : undefined,
      signature: fm.keySymbols.length > 0 ? fm.keySymbols.join(', ') : undefined,
      updatedAt: Date.now(),
    };
    this.nodes.push(node);
    return node;
  }

  /** Whether each line (0-based) is inside a fenced code block, fences included. */
  private fenced?: boolean[];
  private fencedLines(): boolean[] {
    if (this.fenced) return this.fenced;
    const fenced = new Array<boolean>(this.lines.length).fill(false);
    let open: { char: string; len: number } | undefined;
    for (let i = 0; i < this.lines.length; i++) {
      const m = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(this.lines[i]!);
      if (open) {
        fenced[i] = true;
        if (m && m[1]![0] === open.char && m[1]!.length >= open.len && m[2]!.trim() === '') open = undefined;
      } else if (m && !(m[1]![0] === '`' && m[2]!.includes('`'))) {
        fenced[i] = true;
        open = { char: m[1]![0]!, len: m[1]!.length };
      }
    }
    this.fenced = fenced;
    return fenced;
  }

  /** One node per ATX heading; returns them in line order with their level. */
  private extractSections(fileNodeId: string, bodyStart: number): Array<{ node: Node; level: number }> {
    const fenced = this.fencedLines();
    const headings: Array<{ line: number; level: number; text: string }> = [];
    for (let i = bodyStart; i < this.lines.length; i++) {
      if (fenced[i]) continue;
      const m = /^ {0,3}(#{1,6})(?:[ \t]+(.*?))?[ \t]*$/.exec(this.lines[i]!);
      if (!m) continue;
      const text = (m[2] ?? '').replace(/(?:^|[ \t]+)#+$/, '').trim();
      if (text === '') continue;
      headings.push({ line: i, level: m[1]!.length, text });
    }

    const slugCounts = new Map<string, number>();
    const sections: Array<{ node: Node; level: number }> = [];
    for (let h = 0; h < headings.length; h++) {
      const { line, level, text } = headings[h]!;
      let endLine = this.lines.length; // 1-based last line
      for (let k = h + 1; k < headings.length; k++) {
        if (headings[k]!.level <= level) { endLine = headings[k]!.line; break; }
      }
      // Trailing blank lines belong to no section.
      while (endLine > line + 1 && this.lines[endLine - 1]!.trim() === '') endLine--;

      const base = githubSlug(text);
      const seen = slugCounts.get(base);
      const slug = seen === undefined ? base : `${base}-${seen}`;
      slugCounts.set(base, (seen ?? 0) + 1);

      const startLine = line + 1;
      const node: Node = {
        id: this.nodeIds.generate(this.filePath, 'module', text, startLine, 0),
        kind: 'module',
        name: text,
        qualifiedName: `${this.filePath}#${slug}`,
        filePath: this.filePath,
        language: 'markdown',
        startLine,
        endLine,
        startColumn: 0,
        endColumn: this.lines[endLine - 1]?.length ?? 0,
        signature: `${'#'.repeat(level)} ${text}`,
        updatedAt: Date.now(),
      };
      this.nodes.push(node);
      this.edges.push({ source: fileNodeId, target: node.id, kind: 'contains' });
      sections.push({ node, level });
    }
    return sections;
  }

  /** Inline `[label](target)` links to `.md` targets, outside fences and code spans. */
  private extractLinks(fileNodeId: string, sections: Array<{ node: Node; level: number }>, bodyStart: number): void {
    const fenced = this.fencedLines();
    const bySlug = new Map<string, string>();
    for (const s of sections) bySlug.set(s.node.qualifiedName.slice(this.filePath.length + 1), s.node.id);
    const link = /!?\[(?:[^\]\\]|\\.)*\]\(\s*<?([^)\s>]+)>?(?:\s+(?:"[^"]*"|'[^']*'))?\s*\)/g;

    for (let i = bodyStart; i < this.lines.length; i++) {
      if (fenced[i]) continue;
      const text = blankCodeSpans(this.lines[i]!);
      if (!text.includes('](')) continue;
      const lineNo = i + 1;
      // Innermost section holding the line: the last one starting at or above it
      // whose span reaches it (spans nest, so the deepest is the latest start).
      let from = fileNodeId;
      for (const s of sections) {
        if (s.node.startLine > lineNo) break;
        if (s.node.endLine >= lineNo) from = s.node.id;
      }
      link.lastIndex = 0;
      let m;
      while ((m = link.exec(text))) {
        if (m[0].startsWith('!')) continue; // images
        const target = m[1]!;
        if (target.startsWith('#')) {
          const slug = safeDecode(target.slice(1)).toLowerCase();
          const to = bySlug.get(slug);
          if (to && to !== from) {
            this.edges.push({ source: from, target: to, kind: 'references', line: lineNo, column: m.index });
          }
          continue;
        }
        this.addLinkReference(from, target, lineNo, m.index);
      }
    }
  }

  /**
   * A reference to `target` (`path.md` or `path.md#slug`, relative to this
   * file, or project-relative when it starts with `/`). Non-`.md` targets,
   * URLs and paths leaving the project are skipped.
   */
  private addLinkReference(fromNodeId: string, target: string, line: number, column: number): void {
    if (/^[a-z][a-z0-9+.-]*:/i.test(target)) return; // http:, mailto:, file: …
    const hash = target.indexOf('#');
    const rawPath = safeDecode(hash < 0 ? target : target.slice(0, hash)).split('?')[0]!;
    if (!/\.md$/i.test(rawPath)) return;
    const resolved = rawPath.startsWith('/')
      ? path.posix.normalize(rawPath.slice(1))
      : path.posix.normalize(path.posix.join(path.posix.dirname(this.filePath), rawPath));
    if (resolved.startsWith('../') || resolved === '..') return;
    const slug = hash < 0 ? '' : safeDecode(target.slice(hash + 1)).toLowerCase();
    this.unresolvedReferences.push({
      fromNodeId,
      referenceName: slug ? `${resolved}#${slug}` : resolved,
      referenceKind: 'references',
      line,
      column,
      filePath: this.filePath,
      language: 'markdown',
    });
  }
}

/**
 * GitHub's heading anchor: the rendered text lowercased, with everything but
 * letters, digits, marks, spaces, `-` and `_` removed and each space turned
 * into `-` (runs are not collapsed). Link and image syntax renders as its text.
 */
export function githubSlug(heading: string): string {
  const rendered = heading
    .replace(/!?\[([^\]]*)\]\([^)]*\)/g, '$1')
    .replace(/<[^>]+>/g, '');
  return rendered
    .toLowerCase()
    .replace(/[^\p{L}\p{M}\p{N}\p{Pc} -]/gu, '')
    .replace(/ /g, '-');
}

/** `line` with the contents of its inline code spans blanked (same length). */
function blankCodeSpans(line: string): string {
  if (!line.includes('`')) return line;
  return line.replace(/(`+)([\s\S]*?)\1/g, (all) => ' '.repeat(all.length));
}

function safeDecode(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s;
  }
}

function unquote(s: string): string {
  const t = s.trim();
  if (t.length >= 2 && ((t[0] === '"' && t.endsWith('"')) || (t[0] === "'" && t.endsWith("'")))) return t.slice(1, -1);
  return t;
}

function inlineList(value: string): string[] {
  const v = value.trim();
  if (!v.startsWith('[') || !v.endsWith(']')) return [unquote(v)];
  const out: string[] = [];
  // Split on commas outside quotes.
  let cur = '';
  let quote: string | undefined;
  for (const ch of v.slice(1, -1)) {
    if (quote) {
      if (ch === quote) quote = undefined;
      cur += ch;
    } else if (ch === '"' || ch === "'") {
      quote = ch;
      cur += ch;
    } else if (ch === ',') {
      if (cur.trim()) out.push(unquote(cur));
      cur = '';
    } else cur += ch;
  }
  if (cur.trim()) out.push(unquote(cur));
  return out;
}
