"""Rename proof-local names that are never referenced to `_` (the linter's suggested fix).

usage: python -X utf8 apply_unused_names.py LINTDIR MODULE [MODULE ...]
Handles `Variable name `x` is not explicitly referenced` warnings that do NOT point at a `have x`, a
`set ... with x`, or a binder of a declaration signature (those are handled elsewhere or are API).
The token at the warning position must equal the name; it becomes `_`, so the hypothesis stays in
context for automation.  Each module is elaborated with all its renames; on failure, bisected.
"""
import importlib.util
import re
import sys
from pathlib import Path

import stmtx

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
spec = importlib.util.spec_from_file_location('ph', Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\fejer-generators\prune_haves.py'))
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)
W = re.compile(r'(Proofs\w+)\.lean:(\d+):(\d+): warning: Variable name `([^`]+)` is not explicitly referenced')
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance)\b", re.M)


def sig_spans(text):
    out = []
    for h in HEAD.finditer(text):
        e = stmtx.statement_end(text, h.end())
        if e > 0:
            out.append((h.start(), e))
    return out


def candidates(text, warns):
    lines = text.split('\n')
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)
    sigs = sig_spans(text)
    out = []
    for ln, col, var in warns:
        s = lines[ln - 1]
        pre = s[:col]
        if re.fullmatch(r'\s*have\s+', pre) or (re.search(r'\bwith\s+$', pre) and re.match(r'\s*set\s', s)):
            continue
        off = offs[ln - 1] + col
        if any(a <= off < b for a, b in sigs):
            continue
        if not re.match(re.escape(var) + r"(?![\w'₀-₉])", s[col:]) or var == '_':
            continue
        out.append((ln - 1, col, len(var)))
    return out


def apply(text, cands):
    lines = text.split('\n')
    for i, c, n in sorted(cands, key=lambda x: (-x[0], -x[1])):
        lines[i] = lines[i][:c] + '_' + lines[i][c + n:]
    return '\n'.join(lines)


def main():
    lintdir = Path(sys.argv[1])
    scratch = HERE / 'unused_names_scratch.lean'
    for mod in sys.argv[2:]:
        f = lintdir / f'{mod}.txt'
        if not f.exists():
            continue
        warns = [(int(m.group(2)), int(m.group(3)), m.group(4)) for m in W.finditer(f.read_text(encoding='utf8'))
                 if m.group(1) == mod]
        p = GS / f'{mod}.lean'
        text = p.read_text(encoding='utf8')
        cands = candidates(text, warns)
        if not cands:
            continue

        def ok(cs):
            return ph.compiles(apply(text, cs), scratch) if cs else True

        def solve(cs):
            if ok(cs):
                return cs
            if len(cs) == 1:
                return []
            h = len(cs) // 2
            both = solve(cs[:h]) + solve(cs[h:])
            return both if ok(both) else []
        kept = solve(cands)
        if kept:
            p.write_text(apply(text, kept), encoding='utf8', newline='\n')
        print(f'{mod}: {len(kept)}/{len(cands)}', flush=True)


main()
