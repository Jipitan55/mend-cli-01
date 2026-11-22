// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone; run it as
// `node main.ts [options] [PATCH]`. It applies edits in four formats (unified diff, SEARCH/REPLACE
// blocks, V4A patches, JSON edits) to a tree of text files, matching old lines at three tiers
// (exact, trailing-whitespace-insensitive, fully-whitespace-insensitive), and writes every change
// or none. SPEC.md is the whole contract.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands
// over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---- Files: lines, line break, final break (SPEC.md section 3) ----

interface FileParts {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileParts {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(p: FileParts): string {
  if (p.lines.length === 0) return '';
  return p.lines.join(p.br) + (p.final ? p.br : '');
}

const trimEndWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

// ---- Matching lines at three tiers (SPEC.md section 5) ----

function tierEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndWs(a) === trimEndWs(b);
  return trimWs(a) === trimWs(b);
}

/** All 0-based positions where O occurs in lines at the tier. Occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0 || o.length > lines.length) return out;
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!tierEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function tiersToTry(strict: boolean): number[] {
  return strict ? [0] : [0, 1, 2];
}

/** The first tier at which O occurs at least once, with every occurrence there. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; occ: number[] } | null {
  for (const t of tiersToTry(strict)) {
    const occ = occurrences(lines, o, t);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** One line of O or N. `ctx` lines are written as the file's own matched line. */
interface OldNewLine {
  text: string;
  ctx: boolean;
  /** For a context line of N: its index in O. */
  oIdx: number;
}

interface HunkItem {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
  /** True when the patch line was blank (empty or only whitespace), for end-of-body/section trimming. */
  blank: boolean;
}

/** Split a hunk/chunk body into its old lines O and new lines N. */
function splitHunk(items: HunkItem[]): { o: OldNewLine[]; n: OldNewLine[] } {
  const o: OldNewLine[] = [];
  const n: OldNewLine[] = [];
  for (const it of items) {
    if (it.kind === 'ctx') {
      const idx = o.length;
      o.push({ text: it.text, ctx: true, oIdx: -1 });
      n.push({ text: it.text, ctx: true, oIdx: idx });
    } else if (it.kind === 'old') {
      o.push({ text: it.text, ctx: false, oIdx: -1 });
    } else if (it.kind === 'new') {
      n.push({ text: it.text, ctx: false, oIdx: -1 });
    }
  }
  return { o, n };
}

/** Build the lines that replace the matched block: context lines from the file, other lines
 *  re-indented at tier 2 (SPEC.md section 5). */
function buildSegment(fileLines: string[], pos: number, o: OldNewLine[], n: OldNewLine[], tier: number): string[] {
  const out: string[] = [];
  const f = tier === 2 && o.length > 0 ? leadWs(fileLines[pos]!) : '';
  const p = tier === 2 && o.length > 0 ? leadWs(o[0]!.text) : '';
  for (const item of n) {
    if (item.ctx) {
      out.push(fileLines[pos + item.oIdx]!);
      continue;
    }
    const t = item.text;
    if (tier === 2 && t !== '' && !/^[ \t]+$/.test(t) && t.startsWith(p)) out.push(f + t.slice(p.length));
    else out.push(t);
  }
  return out;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful moves, in order, as (old path, new path) pairs, for the `R` output lines. */
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  /** True when a directory (not a regular file) sits at the path on disk. */
  isDir(p: string): boolean {
    try {
      return statSync(p).isDirectory();
    } catch {
      return false;
    }
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- JSON edits (SPEC.md section 9) ----

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null || tree.isDir(p)) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const parts = splitFile(before);
      if (line < 0 || line > parts.lines.length) throw new Fail('no-match', p);
      parts.lines.splice(line, 0, ...add);
      tree.now.set(p, joinFile(parts));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- Unified diffs (SPEC.md section 6) ----

interface Hunk {
  a: number;
  items: HunkItem[];
}

interface UniRaw {
  gitX: string | null;
  gitY: string | null;
  dashOld: string | null;
  dashNew: string | null;
  renFrom: string | null;
  renTo: string | null;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;

function headerPath(line: string): string {
  let s = line.slice(4);
  const tab = s.indexOf('\t');
  if (tab >= 0) s = s.slice(0, tab);
  s = s.trim();
  if (s.startsWith('a/') || s.startsWith('b/')) s = s.slice(2);
  return s;
}

function parseDiffGit(line: string): [string, string] | null {
  const rest = line.slice('diff --git '.length);
  if (!rest.startsWith('a/')) return null;
  const sep = rest.lastIndexOf(' b/');
  if (sep < 0) return null;
  const x = rest.slice(2, sep);
  const y = rest.slice(sep + 3);
  if (x === '' || y === '') return null;
  return [x, y];
}

function parseHunkHeader(line: string, i: number): number {
  const m = HUNK_RE.exec(line);
  if (m === null) throw new Exit2(`error: parse ${i + 1}`);
  return parseInt(m[1]!, 10);
}

/** A hunk's body: lines after the header starting with ` `, `-`, `+`, `\`, or empty. Returns the
 *  body items and the index of the first line after the body. Empty lines at the end of a body
 *  are not part of it. */
function parseHunkBody(lines: string[], start: number): { items: HunkItem[]; next: number } {
  const items: HunkItem[] = [];
  let j = start;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '') {
      items.push({ kind: 'ctx', text: '', blank: true });
      j++;
      continue;
    }
    const c = l[0]!;
    if (c === ' ') {
      items.push({ kind: 'ctx', text: l.slice(1), blank: l.trim() === '' });
      j++;
      continue;
    }
    if (c === '-') {
      items.push({ kind: 'old', text: l.slice(1), blank: false });
      j++;
      continue;
    }
    if (c === '+') {
      items.push({ kind: 'new', text: l.slice(1), blank: false });
      j++;
      continue;
    }
    if (c === '\\') {
      items.push({ kind: 'bs', text: l.slice(1), blank: false });
      j++;
      continue;
    }
    break;
  }
  while (items.length > 0) {
    const last = items[items.length - 1]!;
    if (last.blank) items.pop();
    else break;
  }
  return { items, next: j };
}

/** True when a `\` line follows the hunk's last context or `+` line. */
function lastCtxOrPlusFollowedByBs(items: HunkItem[]): boolean {
  let last = -1;
  for (let i = 0; i < items.length; i++) {
    if (items[i]!.kind === 'ctx' || items[i]!.kind === 'new') last = i;
  }
  if (last < 0) return false;
  return items[last + 1] !== undefined && items[last + 1]!.kind === 'bs';
}

/** Apply a section's hunks in order to the file's lines. Throws Fail('no-match', path). */
function applyHunks(parts: FileParts, hunks: Hunk[], strict: boolean, path: string): FileParts {
  const lines = parts.lines.slice();
  let final = parts.final;
  let d = 0;
  for (const h of hunks) {
    const { o, n } = splitHunk(h.items);
    const noFinal = lastCtxOrPlusFollowedByBs(h.items);
    if (o.length > 0) {
      const found = findTier(lines, o.map((x) => x.text), strict);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let pos = found.occ[0]!;
      let best = Math.abs(pos - target);
      for (const q of found.occ) {
        const dist = Math.abs(q - target);
        if (dist < best) {
          best = dist;
          pos = q;
        }
      }
      const atEnd = pos + o.length === lines.length;
      const seg = buildSegment(lines, pos, o, n, found.tier);
      lines.splice(pos, o.length, ...seg);
      if (atEnd) final = !noFinal;
    } else {
      const p = Math.min(Math.max(h.a + d, 0), lines.length);
      const atEnd = p === lines.length;
      const seg = n.map((x) => x.text);
      lines.splice(p, 0, ...seg);
      if (atEnd) final = !noFinal;
    }
    d += n.length - o.length;
  }
  return { lines, br: parts.br, final };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const raws: UniRaw[] = [];
  let cur: UniRaw | null = null;
  let headerPhase = true;
  const startSection = (git: [string, string] | null): void => {
    cur = {
      gitX: git === null ? null : git[0],
      gitY: git === null ? null : git[1],
      dashOld: null,
      dashNew: null,
      renFrom: null,
      renTo: null,
      create: false,
      del: false,
      hunks: [],
    };
    raws.push(cur);
    headerPhase = true;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (cur === null) {
      if (line.startsWith('diff --git ')) {
        const g = parseDiffGit(line);
        if (g === null) throw new Exit2(`error: parse ${i + 1}`);
        startSection(g);
        i++;
        continue;
      }
      if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        startSection(null);
        cur!.dashOld = headerPath(line);
        cur!.dashNew = headerPath(lines[i + 1]!);
        i += 2;
        continue;
      }
      if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      i++;
      continue;
    }
    if (headerPhase) {
      if (line.startsWith('diff --git ')) {
        const g = parseDiffGit(line);
        if (g === null) throw new Exit2(`error: parse ${i + 1}`);
        startSection(g);
        i++;
        continue;
      }
      if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          cur.dashOld = headerPath(line);
          cur.dashNew = headerPath(lines[i + 1]!);
          i += 2;
          continue;
        }
        throw new Exit2(`error: parse ${i + 2}`);
      }
      if (line.startsWith('rename from ')) {
        cur.renFrom = line.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renTo = line.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (line === 'new file mode' || line.startsWith('new file mode ')) {
        cur.create = true;
        i++;
        continue;
      }
      if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
        cur.del = true;
        i++;
        continue;
      }
      if (line.startsWith('@@')) {
        const a = parseHunkHeader(line, i);
        const body = parseHunkBody(lines, i + 1);
        cur.hunks.push({ a, items: body.items });
        headerPhase = false;
        i = body.next;
        continue;
      }
      i++;
      continue;
    }
    if (line.startsWith('diff --git ')) {
      const g = parseDiffGit(line);
      if (g === null) throw new Exit2(`error: parse ${i + 1}`);
      startSection(g);
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      startSection(null);
      cur!.dashOld = headerPath(line);
      cur!.dashNew = headerPath(lines[i + 1]!);
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      const a = parseHunkHeader(line, i);
      const body = parseHunkBody(lines, i + 1);
      cur.hunks.push({ a, items: body.items });
      i = body.next;
      continue;
    }
    i++;
  }
  return raws.map((r) => unifiedSectionEdit(r, strict));
}

function unifiedSectionEdit(r: UniRaw, strict: boolean): Edit {
  const oldPath = r.dashOld ?? r.renFrom ?? r.gitX;
  const newPath = r.dashNew ?? r.renTo ?? r.gitY;
  const oldIsNull = oldPath === null || oldPath === '/dev/null';
  const newIsNull = newPath === null || newPath === '/dev/null';
  const create = oldIsNull || r.create;
  const del = !create && (newIsNull || r.del);
  return (tree) => {
    if (!oldIsNull && !safe(oldPath!)) throw new Fail('unsafe', oldPath!);
    if (!newIsNull && !safe(newPath!)) throw new Fail('unsafe', newPath!);
    if (create) {
      const np = newPath!;
      if (newIsNull) throw new Fail('unsafe', '/dev/null');
      if (tree.get(np) !== null || tree.isDir(np)) throw new Fail('exists', np);
      const plus: string[] = [];
      let lastPlus: { h: Hunk; idx: number } | null = null;
      for (const h of r.hunks) {
        for (let k = 0; k < h.items.length; k++) {
          if (h.items[k]!.kind === 'new') {
            plus.push(h.items[k]!.text);
            lastPlus = { h, idx: k };
          }
        }
      }
      let noFinal = false;
      if (lastPlus !== null) {
        const nxt = lastPlus.h.items[lastPlus.idx + 1];
        noFinal = nxt !== undefined && nxt.kind === 'bs';
      }
      tree.now.set(np, plus.length === 0 ? '' : plus.join('\n') + (noFinal ? '' : '\n'));
      return;
    }
    if (del) {
      const op = oldPath!;
      if (oldIsNull) throw new Fail('unsafe', '/dev/null');
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    const op = oldPath!;
    const np = newPath!;
    const before = tree.get(op);
    if (before === null) throw new Fail('missing', op);
    if (op !== np && (tree.get(np) !== null || tree.isDir(np))) throw new Fail('exists', np);
    const after = applyHunks(splitFile(before), r.hunks, strict, op);
    const text = joinFile(after);
    if (op === np) {
      tree.now.set(op, text);
    } else {
      tree.now.set(op, null);
      tree.now.set(np, text);
      tree.moves.push([op, np]);
    }
  };
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ----

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchLine + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null || tree.isDir(path)) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const parts = splitFile(before);
    const found = findTier(parts.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const o = oldLines.map((t): OldNewLine => ({ text: t, ctx: false, oIdx: -1 }));
    const n = newLines.map((t): OldNewLine => ({ text: t, ctx: false, oIdx: -1 }));
    const seg = buildSegment(parts.lines, pos, o, n, found.tier);
    parts.lines.splice(pos, oldLines.length, ...seg);
    tree.now.set(path, joinFile(parts));
  };
}

// ---- V4A patches (SPEC.md section 8) ----

interface V4aChunk {
  anchor: string | null;
  eof: boolean;
  items: HunkItem[];
}

type V4aSection =
  | { kind: 'add'; path: string; lines: { text: string; blank: boolean }[] }
  | { kind: 'delete'; path: string }
  | {
      kind: 'update';
      path: string;
      lineNo: number;
      moveTo: string | null;
      chunks: V4aChunk[];
      seenBody: boolean;
      afterEof: boolean;
      curChunk: V4aChunk | null;
    };

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4aSection[] = [];
  let cur: V4aSection | null = null;
  const closeSection = (): void => {
    if (cur === null) return;
    if (cur.kind === 'add') {
      while (cur.lines.length > 0 && cur.lines[cur.lines.length - 1]!.blank) cur.lines.pop();
    } else if (cur.kind === 'update') {
      if (cur.chunks.length === 0 && cur.moveTo === null) throw new Exit2(`error: parse ${cur.lineNo}`);
      const lastChunk = cur.chunks[cur.chunks.length - 1];
      if (lastChunk !== undefined) {
        while (lastChunk.items.length > 0) {
          const it = lastChunk.items[lastChunk.items.length - 1]!;
          if (it.blank) lastChunk.items.pop();
          else break;
        }
      }
    }
    sections.push(cur);
    cur = null;
  };
  const headerOf = (line: string): { kind: 'add' | 'delete' | 'update'; path: string } | null => {
    if (line.startsWith('*** Add File:')) return { kind: 'add', path: line.slice('*** Add File:'.length).trim() };
    if (line.startsWith('*** Delete File:')) return { kind: 'delete', path: line.slice('*** Delete File:'.length).trim() };
    if (line.startsWith('*** Update File:')) return { kind: 'update', path: line.slice('*** Update File:'.length).trim() };
    return null;
  };
  for (let i = first + 1; i < last; i++) {
    const line = lines[i]!;
    const h = headerOf(line);
    if (h !== null) {
      closeSection();
      if (h.kind === 'add') cur = { kind: 'add', path: h.path, lines: [] };
      else if (h.kind === 'delete') cur = { kind: 'delete', path: h.path };
      else cur = { kind: 'update', path: h.path, lineNo: i + 1, moveTo: null, chunks: [], seenBody: false, afterEof: false, curChunk: null };
      continue;
    }
    if (cur === null) {
      if (blank(line)) continue;
      throw new Exit2(`error: parse ${i + 1}`);
    }
    if (cur.kind === 'add') {
      if (line.trim() === '') {
        cur.lines.push({ text: '', blank: true });
        continue;
      }
      if (line.startsWith('+')) {
        cur.lines.push({ text: line.slice(1), blank: false });
        continue;
      }
      throw new Exit2(`error: parse ${i + 1}`);
    }
    if (cur.kind === 'delete') {
      if (blank(line)) continue;
      throw new Exit2(`error: parse ${i + 1}`);
    }
    if (line.startsWith('*** Move to:')) {
      if (cur.seenBody || cur.chunks.length > 0 || cur.moveTo !== null) throw new Exit2(`error: parse ${i + 1}`);
      cur.moveTo = line.slice('*** Move to:'.length).trim();
      continue;
    }
    if (line.startsWith('@@')) {
      const anchorText = line.slice(2).trim();
      const chunk: V4aChunk = { anchor: anchorText === '' ? null : anchorText, eof: false, items: [] };
      cur.chunks.push(chunk);
      cur.curChunk = chunk;
      cur.afterEof = false;
      cur.seenBody = true;
      continue;
    }
    if (line.trimEnd() === '*** End of File') {
      if (cur.curChunk === null) throw new Exit2(`error: parse ${i + 1}`);
      cur.curChunk.eof = true;
      cur.curChunk = null;
      cur.afterEof = true;
      cur.seenBody = true;
      continue;
    }
    if (line.trim() === '') {
      if (cur.afterEof) continue;
      cur.seenBody = true;
      if (cur.curChunk === null) {
        const chunk: V4aChunk = { anchor: null, eof: false, items: [] };
        cur.chunks.push(chunk);
        cur.curChunk = chunk;
      }
      cur.curChunk.items.push({ kind: 'ctx', text: '', blank: true });
      continue;
    }
    const c = line[0]!;
    if (c === ' ' || c === '-' || c === '+') {
      if (cur.afterEof) throw new Exit2(`error: parse ${i + 1}`);
      cur.seenBody = true;
      if (cur.curChunk === null) {
        const chunk: V4aChunk = { anchor: null, eof: false, items: [] };
        cur.chunks.push(chunk);
        cur.curChunk = chunk;
      }
      const kind = c === ' ' ? 'ctx' : c === '-' ? 'old' : 'new';
      cur.curChunk.items.push({ kind, text: line.slice(1), blank: false });
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  closeSection();
  return sections.map((s) => v4aEdit(s, strict));
}

/** First line at or after `from` equal to the anchor (single line) at the first tier with one. */
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number {
  for (const t of tiersToTry(strict)) {
    for (let i = from; i < lines.length; i++) {
      if (tierEq(lines[i]!, anchor, t)) return i;
    }
  }
  return -1;
}

/** First occurrence of O at or after `from` at the first tier with one; for an end-of-file chunk
 *  only occurrences ending at the file's last line count. */
function findTierFrom(lines: string[], o: string[], from: number, strict: boolean, eof: boolean): { tier: number; pos: number } | null {
  for (const t of tiersToTry(strict)) {
    const occ = occurrences(lines, o, t).filter((p) => p >= from && (!eof || p + o.length === lines.length));
    if (occ.length > 0) return { tier: t, pos: occ[0]! };
  }
  return null;
}

function v4aEdit(s: V4aSection, strict: boolean): Edit {
  if (s.kind === 'add') {
    const path = s.path;
    const text = s.lines.length === 0 ? '' : s.lines.map((l) => l.text).join('\n') + '\n';
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null || tree.isDir(path)) throw new Fail('exists', path);
      tree.now.set(path, text);
    };
  }
  if (s.kind === 'delete') {
    const path = s.path;
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  const path = s.path;
  const moveTo = s.moveTo;
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && (tree.get(moveTo) !== null || tree.isDir(moveTo))) throw new Fail('exists', moveTo);
    const parts = splitFile(before);
    let cursor = 0;
    for (const chunk of s.chunks) {
      if (chunk.anchor !== null) {
        const idx = findAnchor(parts.lines, chunk.anchor, cursor, strict);
        if (idx < 0) throw new Fail('no-match', path);
        cursor = idx + 1;
      }
      const { o, n } = splitHunk(chunk.items);
      if (o.length === 0) {
        const pos = chunk.eof ? parts.lines.length : cursor;
        const seg = n.map((x) => x.text);
        parts.lines.splice(pos, 0, ...seg);
        cursor = pos + seg.length;
      } else {
        const found = findTierFrom(parts.lines, o.map((x) => x.text), cursor, strict, chunk.eof);
        if (found === null) throw new Fail('no-match', path);
        const seg = buildSegment(parts.lines, found.pos, o, n, found.tier);
        parts.lines.splice(found.pos, o.length, ...seg);
        cursor = found.pos + seg.length;
      }
    }
    const text = joinFile(parts);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, text);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, text);
    }
  };
}

// ---- Running the CLI (SPEC.md sections 1, 2 and 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Output rows, in byte order of the paths (a move sorts by its new path, section 2).
  const consumedA = new Set<string>();
  const consumedD = new Set<string>();
  const rows: { key: string; line: string }[] = [];
  const next = new Map<string, string>();
  for (const [o, n] of tree.moves) {
    if (!next.has(o)) next.set(o, n);
  }
  const isNew = new Set<string>(tree.moves.map(([, n]) => n));
  for (const [o, n] of tree.moves) {
    if (isNew.has(o)) continue;
    let end = n;
    const seen = new Set<string>([o]);
    while (next.has(end) && !seen.has(end) && tree.original(end) === null && tree.get(end) === null) {
      seen.add(end);
      end = next.get(end)!;
    }
    if (tree.original(o) !== null && tree.get(o) === null && tree.original(end) === null && tree.get(end) !== null) {
      rows.push({ key: end, line: `R ${o} -> ${end}` });
      consumedD.add(o);
      consumedA.add(end);
    }
  }
  for (const p of [...tree.now.keys()]) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (was === null && consumedA.has(p)) continue;
    if (now === null && consumedD.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const now = tree.now.get(p)!;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
