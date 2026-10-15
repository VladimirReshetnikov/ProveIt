"""For each frontier edge U -> D of the final route, the declarations of U that must leave U before
the import can be dropped: those using a constant from a module that U's other imports do not
reach, closed under same-module use.  Also: whether any of them is used by the final route (it must
not be), and how many modules import U directly from outside the final closure.

usage: edge_moves.py used_ranges.txt decl_needs.txt out.json
"""
import collections
import json
import os
import re
import sys

LEAN = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean'


def src(m):
    p = os.path.join(LEAN, *m.split('.')) + '.lean'
    return open(p, encoding='utf8').read() if os.path.exists(p) else ''


allmods = ['GowersSzemeredi.' + f[:-5] for f in os.listdir(os.path.join(LEAN, 'GowersSzemeredi')) if f.endswith('.lean')]
imp = {m: re.findall(r'^import (GowersSzemeredi\.\S+)', src(m), re.M) for m in allmods}
memo = {}


def clo(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | clo(d)
    return memo[m]


root = 'GowersSzemeredi.Proofs18Final'
final = clo(root) | {root}
usedn = {l.split()[1] for l in open(sys.argv[1], encoding='utf8')}
usedm = {l.split()[0] for l in open(sys.argv[1], encoding='utf8')} | {root}
dead = final - usedm
needs = collections.defaultdict(dict)   # module -> decl -> (modules, same-module consts)
for l in open(sys.argv[2], encoding='utf8'):
    head, ms, same = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    needs[m][n] = (set(ms.split()), set(same.split()))


def base(n):
    """Source declaration owning an auxiliary constant (`foo._proof_1`, `foo.match_2`, `foo.eq_1`)."""
    parts = n.split('.')
    while len(parts) > 1 and (parts[-1].startswith('_') or re.fullmatch(r'(match|eq|proof|sizeOf_spec|induct)_\d+', parts[-1])
                              or parts[-1] in ('eq_def', 'eq_unfold')):
        parts.pop()
    return '.'.join(parts)


importers = collections.defaultdict(set)
for m, ds in imp.items():
    for d in ds:
        importers[d].add(m)
res = []
for u in sorted(final & usedm):
    for d in imp[u]:
        if d not in dead:
            continue
        avail = set()
        for i in imp[u]:
            if i != d:
                avail |= clo(i) | {i}
        decls = needs.get(u, {})
        bad = {n for n, (ms, _) in decls.items() if ms - avail}
        users = collections.defaultdict(set)
        for n, (_, same) in decls.items():
            for s in same:
                users[s].add(n)
        st = list(bad)
        while st:
            for v in users[st.pop()]:
                if v not in bad:
                    bad.add(v)
                    st.append(v)
        moved = sorted({base(n) for n in bad})
        res.append(dict(u=u, d=d, moved=moved, used=sorted(n for n in bad if n in usedn),
                        outside=sorted(importers[u] - final), dead_lines=None))
json.dump(res, open(sys.argv[3], 'w', encoding='utf8'), indent=1)
for r in res:
    flag = ' USED!' if r['used'] else ''
    print(f"{len(r['moved']):3} moved, {len(r['outside']):3} outside importers  {r['u'].split('.')[1]} -> {r['d'].split('.')[1]}{flag}")
print(len(res), 'edges;', sum(1 for r in res if not r['moved']), 'need no move;',
      sum(len(r['moved']) for r in res), 'declarations to move')
