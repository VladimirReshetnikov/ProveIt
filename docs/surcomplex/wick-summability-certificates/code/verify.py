#!/usr/bin/env python3
"""Reproducible finite checks; these are not proofs of the infinite theorems.

Run from any directory: python3 code/verify.py
Writes ../data/verification.json. Uses only Python's standard library.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial, prod
from pathlib import Path
import json
import random
import time

from wick_certificates import (wick_certificate, value, add, scale, linear,
                               serializable)

SEED = 20260922
rng = random.Random(SEED)
counts = Counter()
started = time.monotonic()


def check(category, condition):
    if not condition:
        raise AssertionError(category)
    counts[category] += 1


def random_value(rank):
    return value(F(rng.randint(-7, 7), rng.randint(1, 3)) for _ in range(rank))


# Exact Hilbert generation formula for the two-quartic model.
h1, h2 = (1, 0, 2, 0, 0), (0, 1, 0, 0, 2)
h3, h4 = (1, 1, 1, 2, 1), (1, 1, 0, 4, 0)
for m1 in range(21):
    for m2 in range(21):
        for s in range(2 * min(m1, m2) + 1):
            q = (m1, m2, 2*m1-s, 2*s, 2*m2-s)
            r, parity = divmod(s, 2)
            coeff = (m1-r-parity, m2-r-parity, parity, r)
            recovered = tuple(sum(a*h[j] for a,h in zip(coeff, (h1,h2,h3,h4)))
                              for j in range(5))
            check("quartic_semigroup_decompositions", min(coeff) >= 0 and q == recovered)

# Compare an independent closed-form criterion against the certificate solver.
for rank in (1, 2, 3):
    zero = value([0]*rank)
    for _ in range(180):
        l1, l2, c11, c12, c22 = [random_value(rank) for _ in range(5)]
        w1, w2 = add(l1, scale(2, c11)), add(l2, scale(2, c22))
        w4 = add(add(l1, l2), scale(4, c12))
        result = wick_certificate([(4,0),(0,4)], [(0,0),(0,1),(1,1)],
                                  [l1,l2], [c11,c12,c22])
        check("quartic_primal_dual_certificates", (result.balance is not None)
              == (min(w1,w2,w4) > zero))
    for _ in range(100):
        g,h,c = [random_value(rank) for _ in range(3)]
        result = wick_certificate([(3,0),(0,3)], [(0,1)], [g,h], [c])
        check("cross_cubic_primal_dual_certificates", (result.balance is not None)
              == (add(add(g,h),scale(3,c)) > zero))
    for _ in range(70):
        alphas = [(3,1,0), (0,3,2), (2,0,3)]
        lambdas, cs = [random_value(rank) for _ in range(3)], [random_value(rank) for _ in range(3)]
        ds = [add(lam,scale(F(1,2),linear(alpha,cs,rank)))
              for alpha,lam in zip(alphas,lambdas)]
        result = wick_certificate(alphas, [(0,0),(1,1),(2,2)], lambdas, cs)
        check("diagonal_primal_dual_certificates", (result.balance is not None)
              == (min(ds) > zero))
    for _ in range(25):
        g,c = random_value(rank),random_value(rank)
        result = wick_certificate([(3,0)], [(0,1)], [g], [c])
        check("empty_vacuum_semigroup_certificates", result.balance is not None)


def edge_counts(beta, edges):
    def rec(n, remaining, ks):
        if n == len(edges):
            if not any(remaining):
                yield ks
            return
        i,j = edges[n]
        bound = remaining[i]//2 if i==j else min(remaining[i],remaining[j])
        for k in range(bound+1):
            rest=list(remaining)
            rest[i]-=k
            rest[j]-=k
            yield from rec(n+1,tuple(rest),ks+(k,))
    yield from rec(0,tuple(beta),())


def grouped_moment(beta, matrix):
    d=len(beta)
    edges=[(i,j) for i in range(d) for j in range(i,d) if matrix[i][j]]
    total=F(0)
    for ks in edge_counts(beta,edges):
        denominator=prod(factorial(k)*(2**k if i==j else 1)
                         for (i,j),k in zip(edges,ks))
        w=F(prod(factorial(n) for n in beta),denominator)
        assert w.denominator==1
        total+=w*prod(matrix[i][j]**k for (i,j),k in zip(edges,ks))
    return total


def recurrence_moment(matrix):
    @lru_cache(None)
    def rec(beta):
        if not any(beta):
            return 1
        i=next(i for i,b in enumerate(beta) if b)
        rest=list(beta)
        rest[i]-=1
        ans=0
        for j,b in enumerate(rest):
            if b:
                reduced=rest[:]
                reduced[j]-=1
                ans+=b*matrix[i][j]*rec(tuple(reduced))
        return ans
    return rec

for matrix in (((2,3),(3,5)), ((0,2),(2,0)), ((1,-2),(-2,3)),
               ((1,2,0),(2,3,-1),(0,-1,2))):
    rec=recurrence_moment(matrix)
    d=len(matrix)
    for beta in product(range(9),repeat=d):
        if sum(beta)<=8:
            check("wick_formula_vs_independent_recurrence",
                  grouped_moment(beta,matrix)==rec(beta))

# Quartic connected counts, independently enumerated labeled halfedge pairings.
def pairings(items):
    if not items:
        yield ()
        return
    first=items[0]
    for j in range(1,len(items)):
        for tail in pairings(items[1:j]+items[j+1:]):
            yield ((first,items[j]),)+tail


def is_connected(n, edges):
    if n==0:
        return False
    seen={0}
    while True:
        old=len(seen)
        for a,b in edges:
            if a in seen or b in seen:
                seen.update((a,b))
        if len(seen)==old:
            return len(seen)==n

z=[F(1)]
connected=[]
for n in range(1,4):
    ps=list(pairings(tuple(range(4*n))))
    z.append(F(len(ps),factorial(n)))
    cn=sum(is_connected(n,tuple((a//4,b//4) for a,b in p)) for p in ps)
    connected.append(F(cn,factorial(n)))
    check("quartic_pairing_totals", len(ps)==prod(range(1,4*n,2)))
log=[F(0)]*4
# z' = (log z)' z, solved coefficient by coefficient.
for n in range(1,4):
    log[n]=z[n]-sum(F(k,n)*log[k]*z[n-k] for k in range(1,n))
    check("connected_log_identity",log[n]==connected[n-1])

# Concrete edge-rewiring instances, including tadpoles and parallel edges.
base_graphs=[(1,[(0,0),(0,0)]),
             (2,[(0,1),(0,1),(0,1)]),
             (3,[(0,1),(1,2),(2,0),(0,0),(1,1),(2,2)])]
for nv,edges in base_graphs:
    chosen=next(j for j in range(len(edges)) if is_connected(nv,edges[:j]+edges[j+1:]))
    a,b=edges[chosen]
    for n in range(1,21):
        lifted=[]
        for r in range(n):
            lifted.extend((r*nv+i,r*nv+j) for h,(i,j) in enumerate(edges) if h!=chosen)
            lifted.append((r*nv+a,((r+1)%n)*nv+b))
        deg=Counter(x for edge in lifted for x in edge)
        base_deg=Counter(x for edge in edges for x in edge)
        check("connected_cyclic_rewiring", is_connected(n*nv,lifted)
              and len(lifted)==n*len(edges)
              and all(deg[r*nv+i]==base_deg[i] for r in range(n) for i in range(nv)))

# Isotropic cancellation: E[(x+i*y)^(4n)] = 0, C=I, exact integer arithmetic.
for n in range(1,13):
    total=0
    for j in range(0,4*n+1,2):
        a,b=4*n-j,j
        df=lambda k: prod(range(1,k,2))
        total+=factorial(4*n)//(factorial(j)*factorial(4*n-j))*(-1)**(j//2)*df(a)*df(b)
    check("isotropic_cancellation",total==0)

sample_inputs={
    "mixed_quartic_obstruction": ([(4,0),(0,4)],[(0,0),(0,1),(1,1)],
                                   [[-1],[-1]],[[2],[0],[2]]),
    "cross_cubic_infinite_coupling": ([(3,0),(0,3)],[(0,1)],
                                      [[-100],[101]],[[0]]),
    "rank_two_positive_boundary": ([(3,0),(0,3)],[(0,1)],
                                    [[0,0],[0,1]],[[0,0]]),
    "rank_two_negative_boundary": ([(3,0),(0,3)],[(0,1)],
                                    [[0,0],[0,-1]],[[0,0]])}
samples={}
for name,(a,e,g,c) in sample_inputs.items():
    samples[name]=serializable(wick_certificate(a,e,list(map(value,g)),list(map(value,c))))

report={"status":"all finite tests passed", "seed":SEED,
        "test_case_definition":"One counted case per call to check(); additional internal certificate assertions are not counted.",
        "cases_by_category":dict(counts), "total_cases":sum(counts.values()),
        "quartic_positive_coupling_coefficients":[str(x) for x in z],
        "quartic_connected_coefficients":[str(x) for x in connected],
        "sample_certificates":samples,
        "limitations":["No proof-assistant verification.",
                       "Finite tests do not prove the infinite or arbitrary-rank theorems.",
                       "The implemented value groups are finite-rank lexicographic rational vectors.",
                       "No general symbolic Hahn field or Hilbert-basis enumeration is implemented.",
                       "Fourier--Motzkin elimination has an explicit resource guard and may be exponential."],
        "elapsed_seconds":round(time.monotonic()-started,3)}
out=Path(__file__).resolve().parents[1]/"data"/"verification.json"
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
