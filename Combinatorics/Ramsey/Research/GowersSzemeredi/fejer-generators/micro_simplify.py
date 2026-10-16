"""Two semantics-preserving line savings, compile-verified per module.

usage: python -X utf8 micro_simplify.py MODULE [MODULE ...]
Candidates in each module:
  * a standalone `classical` line inside a theorem/lemma proof (not in def/abbrev/instance bodies,
    whose terms it could change), dropped;
  * a run of consecutive `rw [..]` / `rewrite [..]` lines at the same indentation and the same
    `at` location, merged into one `rw [a, b, ..]`.
All candidates of a module are applied together and the module elaborated (no olean); on failure the
candidates are bisected so that every kept edit compiles.  Prints `module: kept/candidates, -lines`.
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
RW = re.compile(r'^(\s*)(?:rw|rewrite) \[(.*)\](\s+at\s+(.+?))?\s*$')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|instance|example|structure)\b')


def candidates(lines):
    kind = None
    out = []
    i = 0
    while i < len(lines):
        l = lines[i]
        m = DECL.match(l)
        if m:
            kind = m.group(1)
        if l.strip() == 'classical' and kind in ('theorem', 'lemma', 'example'):
            out.append(('del', i, i + 1, None))
            i += 1
            continue
        r = RW.match(l)
        if r and ('⊢' not in (r.group(4) or '')):
            j = i + 1
            items = [r.group(2)]
            while j < len(lines):
                r2 = RW.match(lines[j])
                if r2 and r2.group(1) == r.group(1) and (r2.group(4) or '') == (r.group(4) or ''):
                    items.append(r2.group(2))
                    j += 1
                else:
                    break
            if j - i >= 2:
                at = r.group(3) or ''
                merged = f"{r.group(1)}rw [{', '.join(items)}]{at}"
                if len(merged) <= 100:
                    out.append(('merge', i, j, merged))
                i = j
                continue
        i += 1
    return out


def apply(lines, cands):
    out = list(lines)
    for kind, a, b, rep in sorted(cands, key=lambda c: -c[1]):
        if kind == 'del':
            del out[a:b]
        else:
            out[a:b] = [rep]
    return '\n'.join(out)


def main():
    scratch = HERE / 'micro_scratch.lean'
    for mod in sys.argv[1:]:
        p = GS / f'{mod}.lean'
        lines = p.read_text(encoding='utf8').split('\n')
        cands = candidates(lines)
        if not cands:
            continue

        def ok(cs):
            return ph.compiles(apply(lines, cs), scratch) if cs else True

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
            p.write_text(apply(lines, kept), encoding='utf8', newline='\n')
        saved = sum((b - a) if k == 'del' else (b - a - 1) for k, a, b, _ in kept)
        print(f'{mod}: {len(kept)}/{len(cands)}, -{saved} lines', flush=True)


main()
