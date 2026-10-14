"""Minimal GowersSzemeredi import graph for the modules in module_needs.txt.

Each module keeps an existing GowersSzemeredi import iff the import's (new) closure contains a module
it needs; needs left uncovered get a direct import.  Reports the new closure of the root and the edits.
usage: min_imports.py module_needs.txt ROOT out.json
"""
import json
import os
import re
import sys

LEAN = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean'
needs = {}
for line in open(sys.argv[1], encoding='utf8'):
    parts = line.split()
    if parts:
        needs[parts[0]] = set(parts[1:])
root = sys.argv[2]


def src(m):
    p = os.path.join(LEAN, *m.split('.')) + '.lean'
    return open(p, encoding='utf8').read() if os.path.exists(p) else ''


old = {m: [d for d in re.findall(r'^import (\S+)', src(m), re.M) if d.startswith('GowersSzemeredi.')] for m in needs}
order, seen = [], set()


def topo(m):
    if m in seen:
        return
    seen.add(m)
    for d in old.get(m, []):
        topo(d)
    order.append(m)


for m in needs:
    topo(m)
new, clo = {}, {}
for m in order:
    if m not in needs:
        new[m], clo[m] = old.get(m, []), set()
        continue
    keep = [i for i in old[m] if (clo.get(i, set()) | {i}) & needs[m]]
    cov = set()
    for i in keep:
        cov |= clo.get(i, set()) | {i}
    add = []
    for n in sorted(needs[m] - cov, key=lambda n: -len(clo.get(n, set()))):
        if n not in cov:
            add.append(n)
            cov |= clo.get(n, set()) | {n}
    new[m] = keep + add
    clo[m] = cov


def closure(g, r):
    s, st = set(), [r]
    while st:
        for d in g.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


a, b = closure(old, root), closure(new, root)
lines = lambda S: sum(src(m).count('\n') for m in S)
print('root closure', len(a), 'modules', lines(a), 'lines ->', len(b), 'modules', lines(b), 'lines')
edits = {m: dict(remove=[i for i in old[m] if i not in new[m]], add=[i for i in new[m] if i not in old[m]])
         for m in needs if set(old[m]) != set(new[m])}
print(len(edits), 'modules change imports;', sum(len(e['remove']) for e in edits.values()), 'removed,',
      sum(len(e['add']) for e in edits.values()), 'added')
json.dump(dict(edits=edits, dropped=sorted(a - b)), open(sys.argv[3], 'w', encoding='utf8'), indent=1)
