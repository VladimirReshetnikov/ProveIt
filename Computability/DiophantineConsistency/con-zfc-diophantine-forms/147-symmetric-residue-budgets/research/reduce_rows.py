#!/usr/bin/env python3
"""Exact elementary row reduction of a sparse quadratic residual system.

Heuristic choices are subordinate to a complete exact row-operation trace.
No mathematical solvability claim is inferred from finite sampling.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path


def dot(a, b):
    if len(a) > len(b):
        a, b = b, a
    return sum(c*b.get(m, 0) for m, c in a.items())


def add_scaled(a, b, q):
    c = dict(a)
    for m, v in b.items():
        c[m] = c.get(m, 0) + q*v
        if not c[m]:
            del c[m]
    return c


def expand(rows):
    out = defaultdict(int)
    for r in rows:
        ts = sorted(r.items())
        for i, (a, c) in enumerate(ts):
            for j in range(i, len(ts)):
                b, d = ts[j]
                out[tuple(sorted(a+b))] += c*d*(1 if i == j else 2)
    return {m: c for m, c in out.items() if c}


def metrics(rows):
    p = expand(rows)
    return {"residuals": len(rows), "row_terms": sum(map(len, rows)),
            "row_height": max(abs(c) for r in rows for c in r.values()),
            "monomials": len(p), "degree": max(map(len, p)),
            "height": max(map(abs, p.values()))}


def reduce(rows):
    rs = [dict(r) for r in rows]
    ops = []
    for run in range(100):
        changed = False
        order = sorted(range(len(rs)), key=lambda i: (dot(rs[i],rs[i]),i))
        for j in order:
            norm = dot(rs[j],rs[j])
            if norm == 0:
                continue
            for i in reversed(order):
                if i == j:
                    continue
                d = dot(rs[i], rs[j])
                q = (2*abs(d)+norm)//(2*norm)*(1 if d >= 0 else -1)
                if q and q*q*norm-2*q*d < 0:
                    rs[i] = add_scaled(rs[i],rs[j],-q)
                    ops.append([i,j,-q])
                    changed = True
        if not changed:
            return rs, ops
    raise RuntimeError('reduction iteration limit')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('source',type=Path)
    ap.add_argument('destination',type=Path)
    args=ap.parse_args()
    d=json.loads(args.source.read_text())
    rows=[{tuple(m):int(c) for c,m in r['terms']} for r in d['residuals']]
    rs,ops=reduce(rows)
    recovered=[dict(r) for r in rs]
    for i,j,q in reversed(ops):
        recovered[i]=add_scaled(recovered[i],recovered[j],-q)
    if recovered != rows:
        raise RuntimeError('exact inverse failed')
    info={'before':metrics(rows),'after':metrics(rs),'operations':len(ops)}
    print(json.dumps(info,indent=2))
    args.destination.mkdir(parents=True,exist_ok=True)
    (args.destination/'row_operations.json').write_text(json.dumps(ops,indent=2)+'\n')
    d['residuals']=[{'label':f'reduced row {i}',
                     'terms':[[c,list(m)] for m,c in sorted(r.items())]} for i,r in enumerate(rs)]
    d['variant']='elementary residual lattice reduction'
    (args.destination/'equation.json').write_text(json.dumps(d,indent=2)+'\n')
    (args.destination/'metrics.json').write_text(json.dumps(info,indent=2)+'\n')


if __name__=='__main__':
    main()
