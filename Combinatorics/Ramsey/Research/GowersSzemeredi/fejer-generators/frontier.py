"""Frontier edges of the final route: used module U -> dead module D.

A module is *used* when it defines a constant in used_ranges.txt.  Dead modules are the rest of the
closure of Proofs18Final.  Prints, for each frontier edge, the dead closure it opens (modules and
lines that are not reachable from Proofs18Final through used-only paths).
usage: frontier.py used_ranges.txt
"""
import collections
import os
import re
import sys

LEAN = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean'


def src(m):
    p = os.path.join(LEAN, *m.split('.')) + '.lean'
    return open(p, encoding='utf8').read() if os.path.exists(p) else ''


imp = {}
root = 'GowersSzemeredi.Proofs18Final'
st, seen = [root], {root}
while st:
    m = st.pop()
    imp[m] = re.findall(r'^import (GowersSzemeredi\.\S+)', src(m), re.M)
    for d in imp[m]:
        if d not in seen:
            seen.add(d)
            st.append(d)
used = {l.split()[0] for l in open(sys.argv[1], encoding='utf8')} | {root}
dead = seen - used
lines = {m: src(m).count('\n') for m in seen}


def dclosure(m):
    s, st = {m}, [m]
    while st:
        for d in imp.get(st.pop(), []):
            if d in dead and d not in s:
                s.add(d)
                st.append(d)
    return s


edges = [(u, d) for u in seen & used for d in imp[u] if d in dead]
print(len(seen), 'modules,', len(dead), 'dead,', sum(lines[m] for m in dead), 'dead lines;',
      len(edges), 'frontier edges from', len({u for u, _ in edges}), 'used modules')
by_d = collections.defaultdict(list)
for u, d in edges:
    by_d[d].append(u)
rows = []
for d, us in by_d.items():
    c = dclosure(d)
    rows.append((sum(lines[m] for m in c), d, us, len(c)))
rows.sort(reverse=True)
for n, d, us, k in rows[:40]:
    print(f"{n:6} {k:3} {d.split('.')[1]:45} <- {', '.join(u.split('.')[1] for u in us)}")
