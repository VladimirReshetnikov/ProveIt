#!/usr/bin/env python3
"""Exact checks for the completion-budget affine energy theorem.

No third-party modules. All identities and inequalities use integers.
Finite tests supplement the written proof and do not establish novelty.
"""
from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import random

if not __debug__:
    raise SystemExit("Run without Python -O/-OO; assertions must be active.")


class Group:
    def __init__(self, factors):
        self.factors = tuple(factors)
        self.elements = list(itertools.product(*(range(n) for n in factors)))
        self.n = len(self.elements)
        index = {x: i for i, x in enumerate(self.elements)}
        self.add = [[index[tuple((a+b) % n for a,b,n in zip(x,y,factors))]
                     for y in self.elements] for x in self.elements]
        self.neg = [index[tuple((-a) % n for a,n in zip(x,factors))]
                    for x in self.elements]
        self.sub = [[self.add[x][self.neg[y]] for y in range(self.n)]
                    for x in range(self.n)]


def histogram(points, operation):
    return Counter(operation[x][y] for x in points for y in points)


def check(f, domain, target, counts):
    N = domain.n
    S = [x for x in range(N) if f[x]]
    T = [x for x in range(N) if not f[x]]
    s = len(S)
    fibres = {}
    for x in S:
        fibres.setdefault(f[x], []).append(x)
    n = {a: len(v) for a, v in fibres.items()}
    M = sum(v*v for v in n.values())
    A = s*s-M
    C = sum(v*n.get(target.neg[a], 0) for a,v in n.items())
    Z = sum(na*nb*n.get(target.add[a][b], 0)
            for a,na in n.items() for b,nb in n.items())
    rs = histogram(S, domain.sub)
    qs = histogram(S, domain.add)
    ES = sum(v*v for v in rs.values())
    Delta = s**3-ES
    rg = Counter((domain.sub[x][y], target.sub[f[x]][f[y]])
                 for x in S for y in S)
    EG = sum(v*v for v in rg.values())
    E = 0
    for h in range(N):
        derivative = Counter(target.sub[f[domain.add[x][h]]][f[x]]
                             for x in range(N))
        E += sum(v*v for v in derivative.values())
    support = set(S)
    W0 = sum(target.add[f[x]][f[y]] == f[z]
             and domain.sub[domain.add[x][y]][z] in support
             for x in S for y in S for z in S)
    P = sum(sum(rs[h]*v for h,v in histogram(fibre, domain.sub).items())
            for fibre in fibres.values())
    Q = sum(qs[domain.add[x][y]]
            for a, fibre in fibres.items()
            for x in fibre for y in fibres.get(target.neg[a], []))
    exact = (N**3-4*s*N*N+6*s*s*N-4*s**3+ES
             +4*(N-2*s)*M+4*P+2*(N-2*s)*C+2*Q+4*(Z-W0)+EG)
    assert exact == E, ("quadruple partition", f, exact, E)
    assert P <= s*M and Q <= s*C and EG <= ES
    assert 0 <= Z-W0 <= min(Z, Delta)
    assert 0 <= C <= A and 2*Z <= s*A
    if A:
        labels = list(n)
        order_three_pair = (len(labels) == 2
                            and target.neg[labels[0]] == labels[1]
                            and target.add[target.add[labels[0]][labels[0]]][labels[0]] == 0)
        assert (2*Z == s*A) == order_three_pair, ("Schur equality", f)
        counts["schur_equality_checks"] += 1
    cubic = 4*s*N*N-10*s*s*N+6*s**3
    D = N**3-E-cubic
    master = 2*(N-s)*(2*A-C)+2*Delta-4*min(Z, Delta)
    coercive = ((2*N-3*s)*A+2*(N-s)*(A-C)
                +(s*A-2*Z)+2*abs(Delta-Z))
    absolute = (2*N-3*s)*A+2*(N-s)*(A-C)+abs(2*Delta-s*A)
    assert master == coercive and D >= master >= absolute, (
        "completion bound", f, D, master, absolute)
    assert D >= 0, ("global cubic", f, N, s, D)
    if 0 < 3*s < 2*N:
        a = S[0]
        shifted = {domain.sub[x][a] for x in S}
        coset = all(domain.add[x][y] in shifted for x in shifted for y in shifted)
        assert (D == 0) == (len(fibres) == 1 and coset), ("positive-range equality", f)
        counts["positive_range_equality_checks"] += 1
        counts["positive_range_equality_cases"] += (D == 0)
    if 3*s == 2*N:
        affine = all(target.add[f[domain.add[x][y]]][f[0]] == target.add[f[x]][f[y]]
                     for x in range(N) for y in range(N))
        assert (D == 0) == affine, ("endpoint affine", f)
        if D == 0:
            assert len(set(f)) == 3 and 0 in set(f)
        counts["endpoint_checks"] += 1
        counts["endpoint_equality_cases"] += (D == 0)
    # Independent signed convolution, verifying the interface with source 59.
    signed = [(x, f[x], 1) for x in S] + [(x, 0, -1) for x in S]
    conv = Counter()
    for x,a,signa in signed:
        for y,b,signb in signed:
            conv[(domain.add[x][y], target.add[a][b])] += signa*signb
    ED = sum(v*v for v in conv.values())
    assert ED == EG+ES+4*P+2*Q-4*W0, ("signed expansion", f)
    old_identity = (N**3-4*s*N*N+N*(6*s*s+4*M+2*C)
                    -4*s**3-8*s*M-4*s*C+4*Z+ED)
    assert E == old_identity, ("source59 signed identity", f)
    counts["map_evaluations"] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent / "data" / "affine_completion_checks.json")
    args = parser.parse_args()
    counts = Counter()
    suites = [((n,), (3,)) for n in range(1, 9)]
    suites += [((n,), (5,)) for n in range(1, 6)]
    suites += [((2,2), (3,)), ((2,2,2), (3,)), ((3,3), (3,)),
               ((2,2), (3,3)), ((3,), (9,)), ((3,), (15,))]
    inventory = []
    for df, tf in suites:
        domain, target = Group(df), Group(tf)
        before = counts["map_evaluations"]
        for f in itertools.product(range(target.n), repeat=domain.n):
            check(f, domain, target, counts)
        size = counts["map_evaluations"]-before
        inventory.append(dict(domain=df, target=tf, maps=size))
        print(f"Exhausted {df} -> {tf}: {size} maps", flush=True)
    exhaustive = counts["map_evaluations"]
    rng = random.Random(2026100701)
    random_suites = [((12,), (3,)), ((17,), (5,)), ((3,5), (9,)),
                     ((2,2,2,2), (3,3)), ((3,3), (5,5)), ((2,3,3), (15,))]
    for df, tf in random_suites:
        domain, target = Group(df), Group(tf)
        for _ in range(400):
            labels = rng.choice([list(range(target.n)), [0,1,target.neg[1]], [1,target.neg[1]]])
            f = [rng.choice(labels) for _ in range(domain.n)]
            check(f, domain, target, counts)
        print(f"Sampled {df} -> {tf}: 400 map evaluations", flush=True)
    result = dict(status="PASS", arithmetic="exact integers", exhaustive_suites=inventory,
                  exhaustive_maps=exhaustive, sampled_map_evaluations=counts["map_evaluations"]-exhaustive,
                  random_seed=2026100701, counters=dict(counts),
                  scope="Finite consistency checks supplement the universal proofs; no Lean verification or publication priority is asserted.")
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
