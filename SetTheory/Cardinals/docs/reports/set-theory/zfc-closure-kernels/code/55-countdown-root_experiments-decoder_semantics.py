#!/usr/bin/env python3
"""Read-only decoder equivalences via ordered binary decision diagrams.

Leaves retain exact exit control and head displacement. Unchanged tape is
implicit. This is an all-tape sufficient equivalence test, not sampling.
"""
from pathlib import Path
from functools import lru_cache
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / 'upstream/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'
rows = {}
for line in TABLE.read_text().splitlines():
    if not line or line.startswith('#'): continue
    q, b, w, d, t = line.split()
    rows[int(q), int(b)] = int(w), (1 if d == 'R' else -1), int(t)
states = sorted({q for q, b in rows})
pure = {q for q in states if all(rows[q, b][0] == b for b in (0, 1))}
# Remove pure states on cycles, so every expansion has a finite exit.
cycles = set()
for start in pure:
    seen=set(); todo=[rows[start,b][2] for b in (0,1)]
    while todo:
        q=todo.pop()
        if q == start:
            cycles.add(start); break
        if q not in pure or q in seen: continue
        seen.add(q); todo.extend(rows[q,b][2] for b in (0,1))
pure -= cycles

nodes = []
unique = {}
def intern(key):
    if key not in unique:
        unique[key] = len(nodes)
        nodes.append(key)
    return unique[key]
def leaf(q,h): return intern(('leaf', q,h))
def node(v,lo,hi):
    if lo == hi: return lo
    return intern(('node',v,lo,hi))
def top(i): return nodes[i][1] if nodes[i][0] == 'node' else 10**9
@lru_cache(None)
def restrict(i, v, bit):
    n=nodes[i]
    if n[0] == 'leaf' or n[1] > v: return i
    if n[1] == v: return n[2+bit]
    return node(n[1],restrict(n[2],v,bit),restrict(n[3],v,bit))
@lru_cache(None)
def mux(v,lo,hi):
    # OBDD variable order is increasing tape coordinate; known repeats vanish.
    lo=restrict(lo,v,0);hi=restrict(hi,v,1)
    if lo==hi:return lo
    m=min(v,top(lo),top(hi))
    if m==v:return node(v,lo,hi)
    return node(m,mux(v,restrict(lo,m,0),restrict(hi,m,0)),
                  mux(v,restrict(lo,m,1),restrict(hi,m,1)))
@lru_cache(None)
def meaning(q,h):
    if q not in pure:return leaf(q,h)
    _,d0,t0=rows[q,0];_,d1,t1=rows[q,1]
    return mux(h,meaning(t0,h+d0),meaning(t1,h+d1))

if __name__ == '__main__':
    groups={}
    for q in states:groups.setdefault(meaning(q,0),[]).append(q)
    same=[qs for qs in groups.values() if len(qs)>1]
    print(json.dumps({'pure_states':len(pure),'cyclic_terminals':sorted(cycles),
                      'bdd_nodes':len(nodes),'equivalent_groups':same},indent=2))
    shifted=[]
    for q in pure:
        for r in pure:
            if q==r:continue
            for h in (-2,-1,1,2):
                if meaning(q,0)==meaning(r,h):shifted.append([q,r,h])
    print('shifted:',json.dumps(shifted))
