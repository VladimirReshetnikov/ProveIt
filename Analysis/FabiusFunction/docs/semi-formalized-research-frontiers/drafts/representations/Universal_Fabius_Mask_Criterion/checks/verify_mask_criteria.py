#!/usr/bin/env python3
"""Exact finite regressions for the universal mask theorems.

Checks continuous geometric-mask zero divisibility through integer polynomial
division, and independently solves the full joint-law kernel equations for
overlapping masks of a finite Bernoulli-coordinate model. This is regression
evidence, not a replacement for the analytic proofs.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def mul(p, q):
    r = [0] * (len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i+j] += x*y
    return trim(r)


def divide(n, d):
    n, d = trim(n), trim(d)
    if len(n) < len(d):
        return [0], n
    q = [F(0)] * (len(n)-len(d)+1)
    while n != [0] and len(n) >= len(d):
        j = len(n)-len(d)
        c = F(n[-1], d[-1])
        q[j] = c
        for i, x in enumerate(d):
            n[i+j] -= c*x
        n = trim(n)
    return trim(q), n


def qproduct(caps):
    p = [1]
    for a in caps:
        p = mul(p, [1]*a)
    return p


def test_geometric():
    total = feasible = 0
    for m in (2, 3, 4):
        for n in range(1, 6):
            masks = list(product((0, 1), repeat=n))
            polys = {e: qproduct([m**(n-i-1) for i in range(n) if e[i]])
                     for e in masks}
            for e in masks:
                for l in masks:
                    prefix = all(sum(e[:j]) >= sum(l[:j]) for j in range(1, n+1))
                    quotient, remainder = divide(polys[e], polys[l])
                    zero_condition = sum(e) >= sum(l) and remainder == [0]
                    assert prefix == zero_condition, (m, n, e, l)
                    if prefix:
                        assert all(x >= 0 and x.denominator == 1 for x in quotient)
                    total += 1
                    feasible += prefix
    return dict(cases=total, dominates=feasible)


def sum_law(mask, coordinates):
    p = [F(1)]
    for keep, coordinate in zip(mask, coordinates):
        if keep:
            p = mul(p, coordinate)
    return p


def coeff(p, k):
    return p[k] if 0 <= k < len(p) else F(0)


def test_overlap():
    coords = []
    for i, a in enumerate((1, 2, 3, 4)):
        p = F(i+2, i+4)
        law = [F(0)]*(a+1)
        law[0], law[a] = 1-p, p
        coords.append(law)
    masks = list(product((0, 1), repeat=4))
    laws = {e: sum_law(e, coords) for e in masks}
    total = feasible = equations = 0
    for e in masks:
        for l in masks:
            pe, pl = laws[e], laws[l]
            ce, cl = laws[tuple(1-x for x in e)], laws[tuple(1-x for x in l)]
            xs = [x for x, p in enumerate(pe) if p]
            ys = [y for y, p in enumerate(pl) if p]
            kernel = {}
            for x in xs:
                for y in ys:
                    rhs = pl[y]*coeff(cl, x-y)
                    rhs -= sum(pe[v]*coeff(ce, x-v)*kernel[v, y] for v in xs if v < x)
                    kernel[x, y] = rhs/(pe[x]*ce[0])
            residuals = []
            for s in range(11):
                for y in ys:
                    lhs = sum(pe[x]*coeff(ce, s-x)*kernel[x, y] for x in xs)
                    rhs = pl[y]*coeff(cl, s-y)
                    residuals.append(lhs-rhs)
            stochastic = all(sum(kernel[x, y] for y in ys) == 1 for x in xs)
            stochastic &= all(v >= 0 for v in kernel.values())
            direct = stochastic and not any(residuals)
            q, r = divide(pe, pl)
            convolution = r == [0] and all(v >= 0 for v in q) and sum(q) == 1
            assert direct == convolution, (e, l)
            if direct:
                # Retaining common coordinates must leave the same criterion.
                e0 = tuple(int(x and not y) for x, y in zip(e, l))
                l0 = tuple(int(y and not x) for x, y in zip(e, l))
                q0, r0 = divide(laws[e0], laws[l0])
                assert r0 == [0] and q0 == q
            total += 1
            feasible += direct
            equations += len(residuals)
    return dict(cases=total, dominates=feasible, joint_equations=equations)


def test_gaussian():
    cases = 0
    table = {(0, 0): [F(1)]}
    for n in range(1, 13):
        for k in range(n+1):
            if k in (0, n):
                table[n, k] = [F(1)]
                continue
            p, r = divide(qproduct(range(n-k+1, n+1)), qproduct(range(1, k+1)))
            assert r == [0]
            left, right = table[n-1, k], [F(0)]*(n-k)+table[n-1, k-1]
            expected = [coeff(left, j)+coeff(right, j) for j in range(max(len(left), len(right)))]
            assert p == trim(expected)
            assert all(x >= 0 and x.denominator == 1 for x in p)
            assert sum(p) == comb(n, k)
            table[n, k] = p
            cases += 1
    positive = [int(x) for x in table[7, 3]]
    negative, rem = divide(qproduct((1, 6)), qproduct((2, 3)))
    assert rem == [0] and negative == [1, -1, 1]
    return dict(gaussian_cases=cases, positive_example=positive,
                negative_example=[int(x) for x in negative])


def main():
    result = dict(status='passed', arithmetic='exact rational and integer',
                  geometric=test_geometric(), overlap=test_overlap(), gaussian=test_gaussian(),
                  scope='Finite regression checks. Countable-mask and arbitrary-noise statements are proved analytically.')
    Path(__file__).with_name('mask_criteria_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
