#!/usr/bin/env python3
"""Independent endpoint-partition enumeration; optional exact check through n=6."""
import argparse
import json
from exact_counts import counts

def partitions(n):
    if n == 0:
        yield (); return
    a=[0]*n
    def visit(k,mx):
        if k == n:
            yield tuple(a); return
        for v in range(mx+2):
            a[k]=v
            yield from visit(k+1,max(mx,v))
    yield from visit(1,0)

def enumerate_counts(n):
    if not isinstance(n,int) or not 0 <= n <= 6:
        raise ValueError('endpoint enumeration supports only 0 <= n <= 6')
    roots=set(); lines=set(); raw=0
    for a in partitions(2*n):
        edges=[tuple(sorted(a[2*i:2*i+2])) for i in range(n)]
        if any(u==v for u,v in edges) or len(set(edges))!=n:
            continue
        raw+=1
        blocks=[[] for _ in range(max(a)+1)] if a else []
        for i,(u,v) in enumerate(edges):
            blocks[u].append(i); blocks[v].append(i)
        root=tuple(sorted(map(tuple,blocks)))
        roots.add(root)
        adj=tuple((i,j) for i in range(n) for j in range(i+1,n)
                  if set(edges[i]) & set(edges[j]))
        lines.add(adj)
    return {'n':n,'endpoint_partitions':raw,'U':len(roots),
            'V':sum(len(set(root))==len(root) for root in roots),'L':len(lines)}

def check(limit=5):
    expected=counts(limit)
    result=[enumerate_counts(n) for n in range(limit+1)]
    for row in result:
        n=row['n']
        for name in ('U','V','L'):
            if row[name] != expected[name][n]:
                raise ArithmeticError(f'endpoint {name} mismatch at {n}')
        if row['endpoint_partitions'] != 2**n*expected['H'][n]:
            raise ArithmeticError(f'weighted endpoint mismatch at {n}')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-index',type=int,choices=range(7),default=5)
    args=ap.parse_args()
    print(json.dumps(check(args.max_index),indent=2,sort_keys=True))
