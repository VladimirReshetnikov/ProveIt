#!/usr/bin/env python3
"""Closed source semantics modulo commutation of disjoint register routines.

The independence relation is conservative: both atoms are closed, neither
contains a halt instruction, and their sets of all read/written registers are
disjoint.  A halt-containing atom is dependent on every other atom.
"""
from collections import defaultdict
from functools import lru_cache
import heapq,json
import grammar_layout as g

labels={};interned={}
affine_enabled=False
affine_symbols={}
def intern(key):
    if key not in interned:
        i=len(labels);interned[key]=i;labels[i]=key
    return interned[key]

@lru_cache(None)
def effects(i):
    key=labels[i]
    if key[0]=='L':
        e=key[1]
        return (frozenset((e[1],)) if e[0] in ('I','D') else frozenset(),e[0]=='H')
    children=key[1] if key[0]=='S' else key[1:]
    parts=[effects(j) for j in children]
    return frozenset.union(*(p[0] for p in parts)),any(p[1] for p in parts)

@lru_cache(None)
def independent(a,b):
    if a==b:return False
    ar,ah=effects(a);br,bh=effects(b)
    if ah or bh:return False
    if not ar&br:return True
    if affine_enabled and a in affine_symbols and b in affine_symbols:
        from affine_atoms import product
        x,y=affine_symbols[a],affine_symbols[b]
        return product(x,y)==product(y,x)
    return False

@lru_cache(None)
def dependence_predecessors(w):
    last={};pred=[]
    for i,sym in enumerate(w):
        pred.append(frozenset(j for previous,j in last.items() if not independent(previous,sym)))
        last[sym]=i
    return tuple(pred)

@lru_cache(None)
def trace_normal(w):
    """Lexicographically first linear extension of the dependence order."""
    preds=dependence_predecessors(w)
    succ=[[] for _ in w];degree=list(map(len,preds))
    for i,ps in enumerate(preds):
        for p in ps:succ[p].append(i)
    ready=[(w[i],i) for i,n in enumerate(degree) if not n];heapq.heapify(ready)
    order=[]
    while ready:
        sym,i=heapq.heappop(ready);order.append(sym)
        for j in succ[i]:
            degree[j]-=1
            if not degree[j]:heapq.heappush(ready,(w[j],j))
    assert len(order)==len(w)
    return tuple(order)

def normalize(nodes,root):
    bounds=g.rot.edge_bounds(nodes)
    if affine_enabled:
        from affine_atoms import recognizer
        getmatrix,witness=recognizer(nodes)
    def result(key,e):
        i=intern(key)
        if affine_enabled:
            matrix=getmatrix(e)
            if matrix is not None:affine_symbols[i]=matrix
        return i
    @lru_cache(None)
    def visit(e):
        if e[0]!='N':return result(('L',e),e)
        a,b=nodes[e[1]];aa,bb=visit(a),visit(b)
        if bounds(a)[1:]==bounds(b)[1:]==(0,0):
            aw=labels[aa][1] if labels[aa][0]=='S' else (aa,)
            bw=labels[bb][1] if labels[bb][0]=='S' else (bb,)
            return result(('S',trace_normal(aw+bw)),e)
        return result(('A',aa,bb),e)
    return visit,visit(('N',root))

def main():
    visit,r=normalize(g.original,g.original_root)
    groups=defaultdict(list)
    for i in g.original:groups[visit(('N',i))].append(i)
    print('normalized classes',len(groups),'old nodes',len(g.original))
    print('equivalent original nodes',[v for v in groups.values() if len(v)>1])
    original=dict(root=r,labels=labels,groups=dict(groups))
    (g.HERE/'trace_normal_original.json').write_text(json.dumps(original,indent=2)+'\n')

if __name__=='__main__':main()
