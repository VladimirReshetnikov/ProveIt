"""Evaluate import-graph edits for the final route.

usage: edit_graph.py edits.json [--apply]
edits.json: {"Module": {"remove": [...], "add": [...]}, ...} (full module names GowersSzemeredi.X)
Reports the closure of Proofs18Final before/after, and the compensating imports that keep the
import closure of every module OUTSIDE the final route unchanged (as a set): a module outside the
final route whose closure shrinks gets direct imports of the maximal lost modules, processed in
topological order so that compensation propagates.  With --apply, writes all edits.
"""
import json
import os
import re
import sys

LEAN = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean'
GS = os.path.join(LEAN, 'GowersSzemeredi')
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
mods = ['GowersSzemeredi.' + f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m.split('.', 1)[1] + '.lean'), encoding='utf8').read() for m in mods}
old = {m: re.findall(r'^import (GowersSzemeredi\.\S+)', src[m], re.M) for m in mods}
edits = json.load(open(sys.argv[1], encoding='utf8'))
new = {m: [d for d in old[m] if d not in edits.get(m, {}).get('remove', [])] +
       [d for d in edits.get(m, {}).get('add', []) if d not in old[m]] for m in mods}


def closures(g):
    memo = {}

    def c(m):
        if m not in memo:
            s = set()
            memo[m] = s
            for d in g.get(m, []):
                s |= {d} | c(d)
        return memo[m]
    for m in mods:
        c(m)
    return memo


root = 'GowersSzemeredi.Proofs18Final'
co = closures(old)
final_old = co[root] | {root}
order, seen = [], set()


def topo(m):
    if m in seen:
        return
    seen.add(m)
    for d in set(old.get(m, [])) | set(new.get(m, [])):
        topo(d)
    order.append(m)


for m in mods:
    topo(m)
comp = {}
cn = {}
for m in order:
    s = set()
    for d in new[m]:
        s |= {d} | cn[d]
    if m not in final_old and m not in edits:
        lost = co[m] - s
        if lost:
            maximal = sorted(x for x in lost if not any(x in co[y] for y in lost if y != x))
            comp[m] = maximal
            new[m] = new[m] + maximal
            for d in maximal:
                s |= {d} | cn[d]
    cn[m] = s
final_new = cn[root] | {root}
lines = lambda S: sum(src[x].count('\n') for x in S)
print('final route:', len(final_old), 'modules', lines(final_old), 'lines ->', len(final_new), 'modules',
      lines(final_new), 'lines')
heavy = [m for m in comp if not os.path.exists(os.path.join(OUT, m.split('.', 1)[1] + '.olean'))]
print(len(comp), 'outside modules get compensating imports (', sum(len(v) for v in comp.values()), 'lines;',
      len(heavy), 'without local olean )')
for m, v in sorted(comp.items())[:30]:
    print('  +', m.split('.', 1)[1], '<-', ', '.join(x.split('.', 1)[1] for x in v))
broken = [m for m in final_new if m in edits and edits[m].get('remove') and False]
if '--apply' in sys.argv:
    for m in set(edits) | set(comp):
        t = src[m]
        for d in edits.get(m, {}).get('remove', []):
            t, k = re.subn(r'^import ' + re.escape(d) + r'[ \t]*\n', '', t, flags=re.M)
            assert k == 1, (m, d)
        extra = [d for d in edits.get(m, {}).get('add', []) if d not in old[m]] + comp.get(m, [])
        if extra:
            ims = list(re.finditer(r'^import .*$', t, re.M))
            if ims:
                t = t[:ims[-1].end()] + ''.join('\nimport ' + d for d in extra) + t[ims[-1].end():]
            else:
                t = ''.join('import ' + d + '\n' for d in extra) + t
        open(os.path.join(GS, m.split('.', 1)[1] + '.lean'), 'w', encoding='utf8', newline='\n').write(t)
    print('applied to', len(set(edits) | set(comp)), 'modules')
json.dump(dict(comp=comp), open('edit_graph_comp.json', 'w', encoding='utf8'), indent=1)
