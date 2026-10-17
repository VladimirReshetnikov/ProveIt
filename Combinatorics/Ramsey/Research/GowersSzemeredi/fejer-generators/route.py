"""Import closures of the final route.

usage: python -X utf8 route.py [MODULE ...]
Prints the size (modules, lines) of the closure of Proofs18CoverFejerAllDegrees (the real final
module, bridges included), of Proofs18Final, and of the stub check's imports; then, for each listed
module, whether it lies in each closure and which closure modules import it directly.
"""
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SCR = Path(__file__).parent
mods = {p.stem for p in GS.glob('*.lean')}
src = {m: (GS / f'{m}.lean').read_text(encoding='utf8') for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}


def clo(roots):
    s, st = set(roots), list(roots)
    while st:
        for d in imp.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


stub_roots = re.findall(r'^import GowersSzemeredi\.(\S+)', (SCR / 'StubFinal.lean').read_text(encoding='utf8'), re.M)
C = {'real': clo(['Proofs18CoverFejerAllDegrees']), 'final': clo(['Proofs18Final']), 'stub': clo(stub_roots)}
lines = lambda S: sum(src[m].count('\n') for m in S if m in src)
for k, S in C.items():
    print(f'{k:6} {len(S):4} modules {lines(S):7} lines')
print('real - stub:', len(C['real'] - C['stub']), 'modules', lines(C['real'] - C['stub']), 'lines')
print('stub - real:', len(C['stub'] - C['real']), 'modules', lines(C['stub'] - C['real']), 'lines')
for m in sys.argv[1:]:
    flags = ' '.join(k for k, S in C.items() if m in S)
    users = sorted(u for u in C['real'] if m in imp.get(u, []))
    print(f'{m}: [{flags}] imported in real by {" ".join(users)}')
