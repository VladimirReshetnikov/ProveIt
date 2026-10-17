"""Near-duplicate pairs (near_dups3.txt) classified by membership in the cone (used_ranges3.txt).

usage: python -X utf8 pairs_in_cone.py
Only a fold of a pair with BOTH copies used shortens the proof of the final theorems; a pair with one
copy used shortens the corpus (and the route's closure only if the other copy's module leaves it).
"""
import re
from pathlib import Path

SCR = Path(__file__).parent
used = set()
for l in open(SCR / 'used_ranges3.txt', encoding='utf8'):
    p = l.split()
    if len(p) >= 2:
        used.add(p[1].split('LeanProofs.GowersSzemeredi.')[-1])
rows = []
for l in open(SCR / 'near_dups3.txt', encoding='utf8'):
    m = re.match(r'\s*\*?([\d.]+)\s+(\d+)\s+(\S+)\s+~\s+(\d+)\s+(\S+)', l)
    if not m:
        continue
    r, n1, a, n2, b = float(m.group(1)), int(m.group(2)), m.group(3), int(m.group(4)), m.group(5)
    da, db = a.split('.', 1)[1], b.split('.', 1)[1]
    ua, ub = da in used, db in used
    rows.append((ua + ub, min(n1, n2), r, a, b, ua, ub))
for k, title in [(2, 'BOTH used'), (1, 'one used'), (0, 'neither used')]:
    sel = [x for x in rows if x[0] == k]
    print(f'== {title}: {len(sel)} pairs, {sum(x[1] for x in sel)} lines in the shorter copies')
    if k == 2:
        for x in sorted(sel, key=lambda x: -x[1]):
            print(f'   {x[2]:.2f} {x[1]:4} {x[3]}  ~  {x[4]}')
