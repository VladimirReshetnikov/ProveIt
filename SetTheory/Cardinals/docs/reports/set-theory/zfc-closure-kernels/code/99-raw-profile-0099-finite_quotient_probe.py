#!/usr/bin/env python3
"""Finite diagnostic only: cylindric profiles with one selector per Eq class."""
from itertools import product
from collections import defaultdict
import json


def stable_cells(n, graph):
    assignments = list(product(range(n), repeat=n))
    ix = {a: i for i, a in enumerate(assignments)}
    def edge(x, y):
        return (graph >> (n*x+y)) & 1
    colors = [tuple(edge(a[i], a[j]) for i in range(n) for j in range(n)) for a in assignments]
    while True:
        ids = {c:i for i, c in enumerate(sorted(set(colors)))}
        cc = [ids[c] for c in colors]
        refined=[]
        for a in assignments:
            reaches=[]
            for j in range(n):
                reaches.append(tuple(sorted({cc[ix[a[:j]+(v,)+a[j+1:]]] for v in range(n)})))
            refined.append((cc[ix[a]],tuple(reaches)))
        if len(set(refined))==len(set(colors)):
            return assignments, cc, ix
        colors=refined


def candidate_relations(n, graph):
    assignments, colors, ix=stable_cells(n,graph)
    all_rs=set()
    for params in product(range(n),repeat=n-2):
        groups=defaultdict(int)
        for x,y in product(range(n),repeat=2):
            groups[colors[ix[(x,y)+params]]] |= 1 << (n*x+y)
        masks=list(groups.values())
        for choice in range(1 << len(masks)):
            r=0
            for i,mask in enumerate(masks):
                if (choice >> i)&1:
                    r |= mask
            all_rs.add(r)
    return all_rs


def epsc(n,graph,rel):
    preds=[sum(1<<x for x in range(n) if (graph >> (n*x+y))&1) for y in range(n)]
    rows=[sum(1<<y for y in range(n) if (rel >> (n*x+y))&1) for x in range(n)]
    allv=(1<<n)-1
    for x in range(n):
        union=0
        for y in range(n):
            if rows[x]>>y&1:
                union |= preds[y]
        if not any((union & (allv ^ p))==0 for p in preds):
            return True, None  # antecedent false
    image=0
    for row in rows:
        image |= row
    for c in range(n):
        if preds[c] & (allv ^ image):
            continue
        if all((rows[x] & (allv ^ preds[c]))==0 for x in range(n) if preds[x]==0 or (preds[c]>>x)&1):
            return True,c
    return False,None


def run(n):
    survivors=[]
    violations=[]
    for graph in range(1 << (n*n)):
        rs=candidate_relations(n,graph)
        bad=next((r for r in sorted(rs) if not epsc(n,graph,r)[0]),None)
        if bad is None:
            survivors.append(graph)
        else:
            violations.append({'graph':graph,'violating_relation':bad,'definable_relations':len(rs)})
    return {'n':n,'graphs_examined':1 << (n*n),'survivors':survivors,'violations':violations,
            'scope':'Finite diagnostic for cylindric models with Eq quotient size n. No general theorem.'}


if __name__=='__main__':
    import argparse
    from pathlib import Path
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=2)
    p.add_argument('--output',default='finite_quotient_probe.json')
    a=p.parse_args()
    d=run(a.n)
    Path(a.output).write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps({k:v for k,v in d.items() if k!='violations'},indent=2))
