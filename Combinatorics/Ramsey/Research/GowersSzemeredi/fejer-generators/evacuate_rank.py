"""Live modules of the real route ranked by how little of them the final theorems use.

usage: python -X utf8 evacuate_rank.py [N]
For each live, editable module: total lines, lines covered by used declarations, the number of
used source declarations, and how many modules (in the real route) become unreachable from
Proofs18CoverFejerAllDegrees if this module alone left the route (its exclusive cone). A module with
few used declarations and a large exclusive cone is a candidate for evacuating the used helpers
upstream, after which it and its exclusive imports can be detached.
"""
import sys
from pathlib import Path

SCR = Path(__file__).parent
sys_argv = list(sys.argv)
sys.argv = [sys.argv[0]]
code = open(SCR / 'regions3.py', encoding='utf8').read().split("# per dead region")[0]
exec(compile(code.replace("print(", "(lambda *a, **k: None)("), 'regions3', 'exec'))
N = int(sys_argv[1]) if len(sys_argv) > 1 else 40

usedby = {}
for n in used:
    if n in owner and not artifact(owner[n], n):
        usedby.setdefault(owner[n], set()).add(base(n))


def closure_without(skip):
    s, st = {'Proofs18CoverFejerAllDegrees'}, ['Proofs18CoverFejerAllDegrees']
    while st:
        for d in imp.get(st.pop(), []):
            if d not in s and d != skip:
                s.add(d)
                st.append(d)
    return s


rows = []
for m in sorted(live - REAL_ONLY):
    if m == 'Proofs18CoverFejerAllDegrees':
        continue
    covered = set()
    for a, b in ranges.get(m, []):
        covered |= set(range(a, b + 1))
    k = len(usedby.get(m, ()))
    if k > 12:
        continue
    excl = REAL - closure_without(m)
    rows.append((L(excl), len(excl), m, nlines[m], len(covered), k, sorted(usedby.get(m, ()))[:6]))
rows.sort(key=lambda r: -r[0])
print('exclusive lines/modules | module (lines, used lines, used decls) | used')
for r in rows[:N]:
    print(f'{r[0]:6} {r[1]:3} | {r[2]} ({r[3]}, {r[4]}, {r[5]}) | {" ".join(x.split(".")[-1] for x in r[6])}')
