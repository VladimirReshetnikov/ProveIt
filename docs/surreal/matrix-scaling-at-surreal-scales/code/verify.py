#!/usr/bin/env python3
"""Exact finite checks for Sharp Matrix-Scaling Stability.

This program checks finite algebraic identities and finite-order examples.
It is not a proof of arbitrary-rank Hahn summability or a Lean formalization.
Requires Python >= 3.10 and SymPy >= 1.12. No floating-point arithmetic is used.
Run from any directory; the report is written next to this package's data/.
"""
from __future__ import annotations

import itertools
import json
import platform
import random
from pathlib import Path
from typing import Sequence
import sympy as sp

SEED = 20260922
RNG = random.Random(SEED)
ROOT = Path(__file__).resolve().parents[1]


def connected(n: int, edges: Sequence[tuple[int, int]]) -> bool:
    parent = list(range(n))
    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in edges:
        parent[find(a)] = find(b)
    return len({find(i) for i in range(n)}) == 1


def trees(n: int, edges: Sequence[tuple[int, int]]) -> list[tuple[int, ...]]:
    return [T for T in itertools.combinations(range(len(edges)), n - 1)
            if connected(n, [edges[e] for e in T])]


def incidence(n: int, edges: Sequence[tuple[int, int]]) -> sp.Matrix:
    full = sp.zeros(n, len(edges))
    for e, (a, b) in enumerate(edges):
        full[a, e], full[b, e] = 1, -1
    return full[:-1, :]


def graph_family(r: int, c: int):
    full = [(i, r + j) for i in range(r) for j in range(c)]
    for mask in range(1 << len(full)):
        es = [e for j, e in enumerate(full) if mask & (1 << j)]
        if len(es) >= r + c - 1 and connected(r + c, es):
            yield r + c, es


def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x + y for x, y in zip(a, b))


def sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x - y for x, y in zip(a, b))


def bottleneck(n: int, es: Sequence[tuple[int, int]], costs, deleted: int):
    s, target = es[deleted]
    adj = [[] for _ in range(n)]
    for j, (a, b) in enumerate(es):
        if j != deleted:
            adj[a].append((b, costs[j]))
            adj[b].append((a, costs[j]))
    answer = None
    def dfs(x, seen, maximum):
        nonlocal answer
        if x == target:
            if answer is None or maximum < answer:
                answer = maximum
            return
        for y, c in adj[x]:
            if y not in seen:
                dfs(y, seen | {y}, c if maximum is None else max(maximum, c))
    dfs(s, {s}, None)
    return answer


def projection_checks(family) -> dict:
    sample = list(family)
    RNG.shuffle(sample)
    sample = sample[:60]
    tree_count = entry_count = 0
    for n, es in sample:
        m = len(es)
        B = incidence(n, es)
        ps = [sp.Rational(RNG.randint(1, 13), RNG.randint(1, 7)) for _ in es]
        W = sp.diag(*ps)
        L = B * W * B.T
        Pi = B.T * L.inv() * B * W
        H = sp.eye(m) - Pi
        Z = sp.S.Zero
        avg = sp.zeros(m)
        for T in trees(n, es):
            BT = B[:, list(T)]
            assert abs(BT.det()) == 1
            restriction = sp.zeros(n - 1, m)
            for j, e in enumerate(T):
                restriction[j, e] = 1
            PiT = B.T * BT.T.inv() * restriction
            assert all(x in (-1, 0, 1) for x in PiT)
            wt = sp.prod(ps[e] for e in T)
            Z += wt
            avg += wt * PiT
            tree_count += 1
        assert L.det() == Z
        assert avg == Z * Pi
        assert Pi * Pi == Pi and H * H == H
        assert B * W * H == sp.zeros(n - 1, m)
        assert H * B.T == sp.zeros(m, n - 1)
        for e in range(m):
            excluded = sum((sp.prod(ps[k] for k in T)
                            for T in trees(n, es) if e not in T), sp.S.Zero)
            assert H[e, e] == excluded / Z
            entry_count += m
    return dict(graphs=len(sample), spanning_trees=tree_count,
                projection_entries=entry_count)


def gap_checks(family) -> dict:
    instances = edges_checked = bridges = tied_deletions = 0
    for n, es in family:
        ts = trees(n, es)
        for rank in (1, 2):
            costs = [tuple(RNG.randint(-3, 5) for _ in range(rank)) for _ in es]
            zero = (0,) * rank
            sums = []
            for T in ts:
                total = zero
                for e in T:
                    total = add(total, costs[e])
                sums.append(total)
            tau = min(sums)
            for e in range(len(es)):
                without = [w for T, w in zip(ts, sums) if e not in T]
                beta = bottleneck(n, es, costs, e)
                if not without:
                    assert beta is None
                    bridges += 1
                else:
                    kappa = sub(min(without), tau)
                    assert beta is not None
                    assert kappa == max(zero, sub(beta, costs[e]))
                    assert kappa >= zero
                    tied_deletions += int(kappa == zero)
                edges_checked += 1
            instances += 1
    return dict(graph_instances=instances, edge_gaps=edges_checked,
                bridges=bridges, zero_gaps=tied_deletions,
                value_groups=["Z", "Z^2 in lexicographic order"])


def hadamard(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a.multiply_elementwise(b)


def normal_series(B: sp.Matrix, ps: list, f: sp.Matrix, degree: int):
    m = len(ps)
    W = sp.diag(*ps)
    Pi = B.T * (B * W * B.T).inv() * B * W
    Pi = Pi.applyfunc(sp.cancel)
    H = sp.eye(m) - Pi
    hs = [sp.zeros(m, 1) for _ in range(degree + 1)]
    exps = [sp.ones(m, 1)] + [sp.zeros(m, 1) for _ in range(degree)]
    for d in range(1, degree + 1):
        rem = sp.zeros(m, 1)
        for k in range(1, d):
            rem += sp.Rational(k, d) * hadamard(hs[k], exps[d-k])
        hs[d] = H * f if d == 1 else -Pi * rem
        hs[d] = hs[d].applyfunc(sp.cancel)
        exps[d] = (hs[d] + rem).applyfunc(sp.cancel)
        assert all(sp.cancel(x) == 0 for x in B * W * exps[d])
        target = H * f if d == 1 else sp.zeros(m, 1)
        assert all(sp.cancel(x) == 0 for x in H * hs[d] - target)
    return hs, exps, H


def valuation_t(expr, t):
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    num, den = sp.fraction(expr)
    def order(poly):
        return min(mon[0] for mon, coeff in sp.Poly(poly, t).terms() if coeff != 0)
    return order(num) - order(den)


def series_checks() -> dict:
    n, es = 5, [(i, 2+j) for i in range(2) for j in range(3)]
    B = incidence(n, es)
    ps = [sp.Rational(2), sp.Rational(3), sp.Rational(5),
          sp.Rational(7), sp.Rational(11), sp.Rational(13)]
    d = 7
    for f in (sp.Matrix([1, 0, 0, 0, 0, 0]), sp.Matrix([1, -2, 3, 1, -1, 2])):
        normal_series(B, ps, f, d)
    t = sp.Symbol('t')
    B2 = incidence(4, [(0, 2), (0, 3), (1, 2), (1, 3)])
    for gamma in (1, 3):
        a, b = 1 - t**gamma, t**gamma
        hs, exps, H = normal_series(B2, [a, b, b, a], sp.Matrix([1, 0, 0, 0]), 6)
        for k in range(1, 7):
            for e, gain in enumerate([gamma, 0, 0, gamma]):
                assert valuation_t(hs[k][e], t) >= gain
                assert valuation_t(exps[k][e], t) >= gain
        assert valuation_t(H[0, 0], t) == gamma
    return dict(constant_weight_examples=2, constant_weight_order=d,
                hahn_laurent_examples=2, hahn_laurent_order=6,
                checked="conservation, cut condition, Taylor coefficient gains")


def chain_checks() -> dict:
    t = sp.Symbol('t')
    entries = 0
    for n in range(2, 7):
        gamma = [1 + (i % 3) for i in range(n-1)]
        aa = [sp.S.Zero] + [t**g for g in gamma] + [sp.S.Zero]
        diag = [1-aa[i]-aa[i+1] for i in range(n)]
        M = sp.zeros(n-1)
        for i in range(n-1):
            M[i, i] = 1/diag[i]+1/diag[i+1]+2/aa[i+1]
            if i+1 < n-1:
                M[i, i+1] = M[i+1, i] = 1/diag[i+1]
        inv = M.inv()
        for i in range(n-1):
            for j in range(n-1):
                assert valuation_t(inv[i,j], t) == sum(gamma[min(i,j):max(i,j)+1])
                entries += 1
    # Symbolic 2x2 normalization and exact multiplicative error formulas.
    a, b, r = sp.symbols('a b r', nonzero=True)
    x = a*r/(b+a*r)
    assert sp.cancel(x/a-1-b*(r-1)/(b+a*r)).subs(b, 1-a).simplify() == 0
    assert sp.cancel((1-x)/b-1-a*(1-r)/(b+a*r)).subs(b, 1-a).simplify() == 0
    assert sp.cancel((x/(1-x))**2 / ((a/b)**2 * r**2)) == 1
    return dict(chain_sizes=list(range(2,7)), inverse_entries=entries,
                symbolic_square_identities=3)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run verification without -O: assertions must be enabled.")
    family = list(graph_family(2,2)) + list(graph_family(2,3)) + list(graph_family(3,3))
    report = dict(status="PASS", seed=SEED, python=platform.python_version(),
                  sympy=sp.__version__, graphs_available=len(family))
    for name, work in [
        ('tree_projection', lambda: projection_checks(family)),
        ('tree_deletion', lambda: gap_checks(family)),
        ('formal_normalization', series_checks),
        ('chain_propagation', chain_checks),
    ]:
        print(f'Checking {name}...', flush=True)
        report[name] = work()
        print(json.dumps(report[name], sort_keys=True), flush=True)
    report['scope'] = ('Exact finite and finite-order checks only; not a formal proof '
                       'of the infinite Hahn-field theorems.')
    output = ROOT/'data'/'verification.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'PASS. Report: {output}', flush=True)


if __name__ == '__main__':
    main()
