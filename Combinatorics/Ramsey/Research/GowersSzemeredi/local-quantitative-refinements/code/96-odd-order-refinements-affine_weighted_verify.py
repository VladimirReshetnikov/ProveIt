#!/usr/bin/env python3
"""Exact rational weighted-map tests, using integer-scaled arithmetic."""
from __future__ import annotations
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
from affine_completion_verify import Group

if not __debug__:
    raise SystemExit("Run without -O/-OO.")


def convolution(points, domain, target=None):
    out = Counter()
    if target is None:
        for x,a in points:
            for y,b in points:
                out[domain.add[x][y]] += a*b
    else:
        for x,u,a in points:
            for y,v,b in points:
                out[(domain.add[x][y], target.add[u][v])] += a*b
    return out


def check(rows, denominator, domain, target, counters):
    b, N, q = denominator, domain.n, target.n
    S = [b-row[0] for row in rows]
    s = sum(S)
    n = [sum(row[a] for row in rows) if a else 0 for a in range(q)]
    M = sum(v*v for v in n)
    A = s*s-M
    C = sum(n[a]*n[target.neg[a]] for a in range(q))
    Z = sum(n[a]*n[c]*n[target.add[a][c]] for a in range(q) for c in range(q))
    ps = [(x,v) for x,v in enumerate(S) if v]
    full = [(x,a,v) for x,row in enumerate(rows) for a,v in enumerate(row) if v]
    restricted = [(x,a,v) for x,a,v in full if a]
    qs = convolution(ps, domain)
    ES = sum(v*v for v in qs.values())
    E = sum(v*v for v in convolution(full,domain,target).values())
    EG = sum(v*v for v in convolution(restricted,domain,target).values())
    Delta = b*s**3-ES
    rs = Counter()
    for x,v in ps:
        for y,w in ps:
            rs[domain.sub[x][y]] += v*w
    P = Q = 0
    for a in range(1,q):
        for x in range(N):
            for y in range(N):
                P += rows[x][a]*rows[y][a]*rs[domain.sub[x][y]]
                Q += rows[x][a]*rows[y][target.neg[a]]*qs[domain.add[x][y]]
    W0 = 0
    for x in range(N):
        for y in range(N):
            for z in range(N):
                w = domain.sub[domain.add[x][y]][z]
                W0 += S[w]*sum(rows[x][a]*rows[y][c]*rows[z][target.add[a][c]]
                               for a in range(1,q) for c in range(1,q)
                               if target.add[a][c])
    assert 0 <= C <= A and 2*Z <= s*A
    assert P <= b*s*M and Q <= b*s*C and EG <= ES
    assert 0 <= b*Z-W0 <= min(b*Z,Delta)
    exact = (N**3*b**4-4*s*N*N*b**3+6*s*s*N*b*b-4*s**3*b+ES
             +4*b*(N*b-2*s)*M+4*P+2*b*(N*b-2*s)*C+2*Q+4*(b*Z-W0)+EG)
    assert E == exact, ("weighted exact identity", rows, b)
    cubic = 4*s*N*N*b**3-10*s*s*N*b*b+6*s**3*b
    D = N**3*b**4-E-cubic
    master = 2*b*(N*b-s)*(2*A-C)+2*Delta-4*min(b*Z,Delta)
    coercive = ((2*N*b-3*s)*A*b+2*(N*b-s)*(A-C)*b
                +(s*A-2*Z)*b+2*abs(Delta-b*Z))
    assert D >= master == coercive
    assert D >= 0, ("weighted cubic", rows, b)
    if 0 < 3*s < 2*N*b:
        deterministic = all(sum(v > 0 for v in row) == 1 for row in rows)
        extremizer = False
        if deterministic:
            f = [row.index(b) for row in rows]
            support = [x for x,a in enumerate(f) if a]
            a = support[0]
            shifted = {domain.sub[x][a] for x in support}
            coset = all(domain.add[x][y] in shifted for x in shifted for y in shifted)
            extremizer = len({f[x] for x in support}) == 1 and coset
        assert (D == 0) == extremizer, ("weighted equality", rows, b)
        counters["positive_range_equality_checks"] += 1
        counters["positive_range_equality_cases"] += (D == 0)
    counters["weighted_inputs"] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent / "data" / "affine_weighted_checks.json")
    args = parser.parse_args()
    counters = Counter()
    suites = [((n,), (3,), 2) for n in range(1,5)]
    suites += [((n,), (3,), 3) for n in range(1,4)]
    suites += [((n,), (5,), 2) for n in range(1,4)]
    suites += [((2,2), (3,), 2)]
    inventory = []
    for df,tf,b in suites:
        domain,target = Group(df),Group(tf)
        rows = [v for v in itertools.product(range(b+1),repeat=target.n) if sum(v)==b]
        before = counters["weighted_inputs"]
        for value in itertools.product(rows, repeat=domain.n):
            check(value,b,domain,target,counters)
        count = counters["weighted_inputs"]-before
        inventory.append(dict(domain=df,target=tf,denominator=b,row_options=len(rows),inputs=count))
        print(df,tf,b,count,flush=True)
    output = dict(status="PASS",arithmetic="exact integers after multiplying rational expressions by denominator^4",
                  suites=inventory,counters=dict(counters),
                  convention="Four labels are sampled independently, including at coincident domain coordinates.")
    args.output.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
