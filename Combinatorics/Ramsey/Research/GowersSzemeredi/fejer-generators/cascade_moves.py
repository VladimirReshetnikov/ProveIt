"""Cascade-aware feasibility of detaching each dead region from the final route.

usage: cascade_moves.py edge_moves_real.json decl_needs2.txt used_ranges_real.txt
For every region (dead component), start from the declarations edge_moves says must leave their
modules, and close under use: a declaration of a final-route module that uses a moved constant must
move too.  The region is INFEASIBLE when the closure contains a declaration the final theorems use.
Prints feasible regions with: lines leaving the route, declarations to move, modules they come from.
"""
import collections
import json
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
edges = json.load(open(sys.argv[1], encoding='utf8'))
used = {l.split()[1] for l in open(sys.argv[3], encoding='utf8')}
users = collections.defaultdict(set)     # constant -> declarations using it
owner = {}
for l in open(sys.argv[2], encoding='utf8'):
    head, ms, same = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    owner[n] = m
    for x in ms.split():
        users[x.split(':', 1)[1]].add(n)
    for x in same.split():
        users[x].add(n)
mods = {f[:-5] for f in os.listdir(GS) if f.endswith('.lean')}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', open(os.path.join(GS, m + '.lean'), encoding='utf8').read(), re.M)
       for m in mods}


def clo(r):
    s, st = set(), [r]
    while st:
        for d in imp.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


final = {'GowersSzemeredi.' + m for m in clo('Proofs18Final') | {'Proofs18Final'}}
usedm = {owner.get(n) for n in used} | {'GowersSzemeredi.Proofs18Final'}
dead = final - usedm
parent = {d: d for d in dead}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for m in dead:
    for d in imp.get(m.split('.', 1)[1], []):
        if 'GowersSzemeredi.' + d in dead:
            parent[find(m)] = find('GowersSzemeredi.' + d)
regions = collections.defaultdict(list)
for e in edges:
    if e['d'] in parent:
        regions[find(e['d'])].append(e)
lines = lambda S: sum(open(os.path.join(GS, x.split('.', 1)[1] + '.lean'), encoding='utf8').read().count('\n') for x in S)
rows = []
for r, es in regions.items():
    moved = set()
    for e in es:
        moved |= {n for n in e['moved']}
    st = list(moved)
    while st:
        c = st.pop()
        for u in users.get(c, ()):
            if u not in moved and owner.get(u) in final:
                moved.add(u)
                st.append(u)
    bad = sorted(n for n in moved if n in used)
    comp = {x for x in dead if find(x) == r}
    src = sorted({owner.get(n, '?').split('.')[-1] for n in moved})
    rows.append((lines(comp), len(comp), len(moved), bool(bad), src, sorted(c.split('.')[-1] for c in comp)[:3]))
rows.sort(key=lambda r: -r[0])
for row in rows[:25]:
    print(f"{row[0]:6} lines {row[1]:3} mods | {row[2]:3} moves {'INFEASIBLE' if row[3] else 'ok        '} | from {', '.join(row[4][:4])} | {', '.join(row[5])}")
