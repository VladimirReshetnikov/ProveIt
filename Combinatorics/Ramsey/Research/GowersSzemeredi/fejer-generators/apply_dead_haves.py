"""Delete dead `have`s and unused `set ... with h` clauses flagged by the unused-variable linter.

usage: python -X utf8 apply_dead_haves.py LINTDIR MODULE [MODULE ...]
For each module: collect `Variable name `h` is not explicitly referenced` warnings that point at
  * `have h ... :=` / `have h := ...` (a tactic `have` at the start of its line): delete the
    statement, i.e. that line and the following lines indented deeper;
  * `set x := e with h`: drop ` with h`.
All candidates of a module are applied together and the module is elaborated (prune_haves.compiles,
no olean written).  On failure, candidates are bisected so that every kept deletion compiles.
Writes the result back and prints `module: kept/candidates`.
"""
import importlib.util
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
spec = importlib.util.spec_from_file_location('ph', Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Research\GowersSzemeredi\fejer-generators\prune_haves.py'))
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)
W = re.compile(r'(Proofs\w+)\.lean:(\d+):(\d+): warning: Variable name `([^`]+)` is not explicitly referenced')


def candidates(mod, text, warns):
    lines = text.split('\n')
    out = []
    for ln, col, var in warns:
        s = lines[ln - 1]
        pre = s[:col]
        if re.fullmatch(r'\s*have\s+', pre) and re.match(re.escape(var) + r"(?![\w'])", s[col:]):
            ind = len(s) - len(s.lstrip())
            j = ln
            while j < len(lines) and lines[j].strip() and len(lines[j]) - len(lines[j].lstrip()) > ind:
                j += 1
            out.append(('del', ln - 1, j))          # delete lines [ln-1, j)
        elif re.search(r'\bwith\s+$', pre) and re.match(r'\s*set\s', s) and \
                re.fullmatch(re.escape(var) + r'\s*', s[col:]):
            out.append(('with', ln - 1, col))
    return out


def apply(text, cands):
    lines = text.split('\n')
    dels = set()
    for kind, a, b in cands:
        if kind == 'del':
            dels.update(range(a, b))
        else:
            s = lines[a]
            lines[a] = re.sub(r'\s+with\s+$', '', s[:b]).rstrip()
    return '\n'.join(l for i, l in enumerate(lines) if i not in dels)


def main():
    lintdir = Path(sys.argv[1])
    for mod in sys.argv[2:]:
        f = lintdir / f'{mod}.txt'
        if not f.exists():
            continue
        warns = [(int(m.group(2)), int(m.group(3)), m.group(4)) for m in W.finditer(f.read_text(encoding='utf8'))
                 if m.group(1) == mod]
        p = GS / f'{mod}.lean'
        text = p.read_text(encoding='utf8')
        cands = candidates(mod, text, warns)
        if not cands:
            continue
        scratch = HERE / 'dead_have_scratch.lean'

        def ok(cs):
            return ph.compiles(apply(text, cs), scratch) if cs else True

        def solve(cs):
            if ok(cs):
                return cs
            if len(cs) == 1:
                return []
            h = len(cs) // 2
            left = solve(cs[:h])
            right = solve(cs[h:])
            both = left + right
            return both if ok(both) else (left if len(left) >= len(right) else right)
        kept = solve(cands)
        if kept:
            p.write_text(apply(text, kept), encoding='utf8', newline='\n')
        print(f'{mod}: {len(kept)}/{len(cands)}', flush=True)


main()
