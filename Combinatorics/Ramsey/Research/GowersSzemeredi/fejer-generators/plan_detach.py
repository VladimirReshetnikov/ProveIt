"""Plan detaching dead regions from the final route.

usage: plan_detach.py edge_moves_real.json decl_needs.txt TARGET_DEAD_MODULE [...]
Cuts every frontier edge U -> D whose D is in the dead component of one of the targets, assuming
U's moved declarations go to a new module outside the final route.  Then checks, for EVERY module of
the new final closure, that each of its declarations (minus moved ones) only needs modules of its new
closure.  Prints the edges, the moves, any violations, and the lines/modules that leave.
"""
import collections
import json
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
mods = ['GowersSzemeredi.' + f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m.split('.', 1)[1] + '.lean'), encoding='utf8').read() for m in mods}
imp = {m: re.findall(r'^import (GowersSzemeredi\.\S+)', src[m], re.M) for m in mods}
root = 'GowersSzemeredi.Proofs18Final'
edges = json.load(open(sys.argv[1], encoding='utf8'))
needs = collections.defaultdict(dict)
for l in open(sys.argv[2], encoding='utf8'):
    head, ms, same = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    needs[m][n] = set(ms.split())


def closures(g):
    memo = {}

    def c(m):
        if m not in memo:
            s = set()
            memo[m] = s
            for d in g.get(m, []):
                s |= {d} | c(d)
        return memo[m]
    for m in g:
        c(m)
    return memo


co = closures(imp)
final = co[root] | {root}
deadset = {e['d'] for e in edges}
# dead component of each target (dead = final minus modules with a real use; approximate by
# the targets' dead closures inside final)
usedm = set()
for e in edges:
    pass
targets = ['GowersSzemeredi.' + t if not t.startswith('GowersSzemeredi.') else t for t in sys.argv[3:]]
sel = [e for e in edges if e['d'] in targets]
g = {m: list(v) for m, v in imp.items()}
moved = collections.defaultdict(set)
for e in sel:
    g[e['u']] = [d for d in g[e['u']] if d != e['d']]
    for n in e['moved']:
        moved[e['u']].add(n)
added = collections.defaultdict(list)
while True:
    cn = closures(g)
    final_new = cn[root] | {root}
    viol = []
    for m in final_new:
        avail = cn[m] | {m}
        lostm = set()
        for n, ms in needs.get(m, {}).items():
            if any(n == x or n.startswith(x + '.') for x in moved.get(m, ())):
                continue
            lostm |= ms - avail
        if lostm:
            viol.append((m, sorted(lostm)))
    if not viol:
        break
    for m, lostm in viol:
        top = [x for x in lostm if not any(x in co[y] for y in lostm if y != x)]
        g[m] = g[m] + top
        added[m] += top
gone = final - final_new
print('re-routing imports:', sum(len(v) for v in added.values()), 'in', len(added), 'modules')
for m, v in added.items():
    print('   +', m.split('.')[1], '<-', ', '.join(x.split('.')[1] for x in v))
lines = lambda S: sum(src[x].count('\n') for x in S)
for e in sel:
    print(f"cut {e['u'].split('.')[1]} -> {e['d'].split('.')[1]}; move {[x.split('.')[-1] for x in e['moved']]}")
print('leave the final route:', len(gone), 'modules,', lines(gone), 'lines')
print(len(viol), 'violations')
for v in []:
    print('  ', v[0].split('.')[1], v[1][-60:], '<-', [x.split('.')[1] for x in v[2]][:3])
json.dump(dict(edges=sel, gone=sorted(gone), added=added), open('plan_detach.json', 'w', encoding='utf8'), indent=1)
