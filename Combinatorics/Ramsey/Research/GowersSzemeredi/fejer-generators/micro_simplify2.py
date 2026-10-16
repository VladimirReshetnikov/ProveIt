"""micro_simplify.py with error attribution instead of blind bisection.

usage: python -X utf8 micro_simplify2.py MODULE [MODULE ...]
Same candidates as micro_simplify.py (drop `classical` in theorem/lemma proofs; merge runs of `rw`
lines).  Per module: apply all, elaborate once; every declaration with an error gets all of its edits
restored; elaborate again to confirm.  If the confirmation still fails, fall back to bisection over
the remaining candidates.  Prints `module: kept/candidates, -lines, compiles`.
"""
import importlib.util
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / 'micro_simplify.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
ms = {'__name__': 'ms', '__file__': str(HERE / 'micro_simplify.py')}
exec(compile(src, 'micro_simplify.py', 'exec'), ms)
ph, GS, candidates, apply = ms['ph'], ms['GS'], ms['candidates'], ms['apply']
HEAD = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?'
                  r'(?:theorem|lemma|def|abbrev|instance|example|structure)\b')


def elaborate(text, scratch):
    scratch.write_text(text, encoding='utf8', newline='\n')
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join(map(str, [ph.OUTPUT] + sorted(ph.PACKAGES.glob('*/.lake/build/lib/lean'))))
    while ph.other_lean_running():
        time.sleep(20)
    r = subprocess.run(['lean', '-DautoImplicit=false', str(scratch)], cwd=ph.ROOT, env=env, capture_output=True,
                       text=True, encoding='utf8', errors='replace')
    out = r.stdout + r.stderr
    errs = [int(m.group(1)) for m in re.finditer(r'\.lean:(\d+):\d+: error', out)]
    return (r.returncode == 0 and not errs), errs


def decl_of_line(lines, ln):
    """index of the declaration header at or above line ln (0-based)"""
    for i in range(min(ln, len(lines) - 1), -1, -1):
        if HEAD.match(lines[i]):
            return i
    return -1


def main():
    scratch = HERE / 'micro2_scratch.lean'
    for mod in sys.argv[1:]:
        p = GS / f'{mod}.lean'
        lines = p.read_text(encoding='utf8').split('\n')
        cands = candidates(lines)
        if not cands:
            continue
        compiles = 0
        # map each candidate to the declaration containing it (in the original numbering)
        owner = {c: decl_of_line(lines, c[1]) for c in cands}
        kept = list(cands)
        ok, errs = elaborate(apply(lines, kept), scratch)
        compiles += 1
        if not ok:
            # translate error lines of the edited text back to original line numbers
            edited_to_orig = []
            removed = {}
            for kind, a, b, rep in kept:
                removed[a] = (b - a) if kind == 'del' else (b - a - 1)
            i = 0
            while i < len(lines):
                c = next((c for c in kept if c[1] == i), None)
                if c is None:
                    edited_to_orig.append(i)
                    i += 1
                elif c[0] == 'del':
                    i = c[2]
                else:
                    edited_to_orig.append(i)
                    i = c[2]
            bad = set()
            for ln in errs:
                k = ln - 1
                orig = edited_to_orig[k] if 0 <= k < len(edited_to_orig) else len(lines) - 1
                bad.add(decl_of_line(lines, orig))
            kept = [c for c in kept if owner[c] not in bad]
            ok, errs = elaborate(apply(lines, kept), scratch) if kept else (True, [])
            compiles += 1
            if not ok:
                def good(cs):
                    nonlocal compiles
                    compiles += 1
                    return elaborate(apply(lines, cs), scratch)[0] if cs else True

                def solve(cs):
                    if good(cs):
                        return cs
                    if len(cs) == 1:
                        return []
                    h = len(cs) // 2
                    both = solve(cs[:h]) + solve(cs[h:])
                    return both if good(both) else []
                kept = solve(kept)
        if kept:
            p.write_text(apply(lines, kept), encoding='utf8', newline='\n')
        saved = sum((b - a) if k == 'del' else (b - a - 1) for k, a, b, _ in kept)
        print(f'{mod}: {len(kept)}/{len(cands)}, -{saved} lines, {compiles} compiles', flush=True)


main()
