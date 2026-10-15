"""Gain of cutting frontier edges, region by region, and all at once.

A region is the set of frontier edges sharing a dead target's weakly connected dead component.
For each region: lines/modules leaving the final route if all its frontier edges are cut (with
re-routing of used modules that were reachable only through the region), declarations to move.
usage: region_gain.py edge_moves.json used_ranges.txt
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
usedm = {l.split()[0] for l in open(sys.argv[2], encoding='utf8')} | {root}


def closure(g, r):
    s, st = set(), [r]
    while st:
        for d in g.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


final = closure(imp, root) | {root}
dead = final - usedm
# dead components (undirected, inside dead)
parent = {d: d for d in dead}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for m in dead:
    for d in imp[m]:
        if d in dead:
            parent[find(m)] = find(d)
regions = collections.defaultdict(list)
for e in edges:
    regions[find(e['d'])].append(e)
lines = lambda S: sum(src[x].count('\n') for x in S)


def cut(es):
    g = {m: list(v) for m, v in imp.items()}
    for e in es:
        g[e['u']] = [d for d in g[e['u']] if d != e['d']]
    # re-route: used modules that fell out are imported directly by Proofs18Final's side (count only)
    after = closure(g, root) | {root}
    lost_used = (final - after) & usedm
    for u in lost_used:
        g[root] = g[root] + [u]
    after = closure(g, root) | {root}
    return final - after, lost_used


rows = []
for r, es in regions.items():
    gone, lost_used = cut(es)
    rows.append((lines(gone), len(gone), len(es), sum(len(e['moved']) for e in es), len(lost_used),
                 sorted({e['d'].split('.')[1] for e in es})[:3]))
rows.sort(reverse=True)
for row in rows[:25]:
    print(f"{row[0]:6} lines {row[1]:3} mods | {row[2]:2} edges {row[3]:3} moves | reroute {row[4]} | {', '.join(row[5])}")
gone, lost_used = cut(edges)
print('ALL:', lines(gone), 'lines', len(gone), 'modules leave;', len(edges), 'edges,',
      sum(len(e['moved']) for e in edges), 'moves, reroute', len(lost_used))
