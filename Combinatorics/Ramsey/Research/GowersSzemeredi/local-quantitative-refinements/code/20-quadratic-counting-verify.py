#!/usr/bin/env python3
"""Reproducible finite checks for Quadratic Counting Errors.

All checks except --gauss use Fraction/integer arithmetic and Python's
standard library. These tests supplement, and do not replace, the proofs.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import product, combinations
from math import gcd, prod, sqrt
from random import Random
from pathlib import Path
import json


def cube_power(f: tuple[F, ...], subgroups: tuple[tuple[int, ...], ...]) -> F:
    """Real directional cube power, computed by derivative recursion."""
    n = len(f)
    if not subgroups:
        return sum(f, F(0)) / n
    hlast, *rest = subgroups
    return sum((cube_power(tuple(f[x] * f[(x+h) % n] for x in range(n)),
                           tuple(rest)) for h in hlast), F(0)) / len(hlast)


def image(n: int, d: int) -> tuple[int, ...]:
    return tuple(range(0, n, gcd(n, d)))


def average(fs: list[tuple[F, ...]], slopes: tuple[int, ...]) -> F:
    n = len(fs[0])
    return sum((prod(fs[i][(x+c*y) % n] for i, c in enumerate(slopes))
                for x in range(n) for y in range(n)), F(0)) / n**2


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', default='verification_report.json')
    ap.add_argument('--gauss', action='store_true', help='also run NumPy floating-point check')
    args = ap.parse_args()
    rng = Random(20261006)
    counts: dict[str, int] = {}
    alphabet = [F(-1), F(-1, 2), F(0), F(1, 2), F(1)]

    # Every ordered triple on the two-element group with f_i in {-1,0,1}^G.
    checks = 0
    vectors = list(product((F(-1), F(0), F(1)), repeat=2))
    for slopes in ((0, 1, 2), (0, 0, 1), (0, 0, 0)):
        for fs0 in product(vectors, repeat=3):
            fs = list(fs0)
            qs = [cube_power(fs[i], tuple(image(2, slopes[i]-slopes[j])
                                         for j in range(3) if i != j)) for i in range(3)]
            val = average(fs, slopes)
            for i, j in combinations(range(3), 2):
                ell = next(t for t in range(3) if t not in (i, j))
                l2sq = sum(v*v for v in fs[ell]) / 2
                assert val**4 <= qs[i]*qs[j]*l2sq**2
                checks += 1
    counts['exhaustive_two_function_L2_inequalities'] = checks

    checks = 0
    for n, k, trials in ((3,3,40),(4,3,40),(5,3,40),(6,3,30),
                         (3,4,30),(4,4,25),(5,4,20),(3,5,12)):
        for _ in range(trials):
            slopes = tuple(rng.randrange(n) for _ in range(k))
            fs = [tuple(rng.choice(alphabet) for _ in range(n)) for _ in range(k)]
            pwr = 2**(k-1)
            qs = [cube_power(fs[i], tuple(image(n, slopes[i]-slopes[j])
                                         for j in range(k) if i != j)) for i in range(k)]
            assert min(qs) >= 0
            val = average(fs, slopes)
            for i, j in combinations(range(k), 2):
                for ell in range(k):
                    if ell in (i,j):
                        continue
                    l2sq = sum(v*v for v in fs[ell]) / n
                    infprod = prod(max(abs(v) for v in fs[t]) for t in range(k)
                                   if t not in (i,j,ell))
                    assert val**pwr <= qs[i]*qs[j]*l2sq**(pwr//2)*infprod**pwr
                    checks += 1
    counts['random_rational_two_function_L2_inequalities'] = checks

    compare, equality = 0, 0
    for n in range(2,9):
        divs = [d for d in range(1,n+1) if n%d == 0]
        for s in (2,3):
            for _ in range(18):
                ds = [rng.choice(divs) for _ in range(s)]
                hs = tuple(tuple(range(0,n,d)) for d in ds)
                f = tuple(rng.choice(alphabet) for _ in range(n))
                q = cube_power(f, hs)
                u = cube_power(f, (tuple(range(n)),)*s)
                assert 0 <= q <= prod(ds)*u
                compare += 1
                intersection = set.intersection(*(set(h) for h in hs))
                shift = rng.randrange(n)
                support = {(x+shift)%n for x in intersection}
                g = tuple(rng.choice(alphabet) if x in support else F(0) for x in range(n))
                assert cube_power(g, hs) == prod(ds)*cube_power(g,(tuple(range(n)),)*s)
                equality += 1
    counts['finite_index_comparisons'] = compare
    counts['coset_supported_exact_equalities'] = equality

    checks = 0
    for k in range(2,9):
        for _ in range(100):
            a = [F(rng.randrange(5),4) for _ in range(k)]
            d = [F(rng.randrange(5),4) for _ in range(k)]
            b = [x-y for x,y in zip(a,d)]
            rhs = prod(d) + sum(b[i]*prod(d[r] for r in range(k) if r != i) for i in range(k))
            rhs += sum(prod(d[r] for r in range(j) if r != i)*b[i]*b[j]*prod(a[r] for r in range(j+1,k))
                       for i in range(k) for j in range(i+1,k))
            assert prod(a) == rhs
            checks += 1
    counts['first_two_residual_identities'] = checks

    # Strong k=3 indicator bound: error^2 <= delta(1-delta) U2^4.
    checks = 0
    for n in (3,5,7,9):
        for bits in product((0,1), repeat=n):
            f = tuple(F(v) for v in bits)
            delta = sum(f)/n
            b = tuple(v-delta for v in f)
            q = cube_power(b,(tuple(range(n)),)*2)
            err = average([f,f,f],(0,1,2))-delta**3
            assert err*err <= delta*(1-delta)*q
            checks += 1
    counts['exhaustive_three_AP_indicator_bounds'] = checks

    # A squared-power rational consequence of B_k <= sqrt(delta) T_k.
    checks = 0
    for n,k,trials in ((5,4,45),(7,4,35),(5,5,25)):
        for _ in range(trials):
            f = tuple(F(rng.randrange(2)) for _ in range(n))
            delta = sum(f)/n
            b = tuple(v-delta for v in f)
            q = cube_power(b,(tuple(range(n)),)*(k-1))
            err = abs(average([f]*k, tuple(range(k)))-delta**k)
            t = sum(F(r+1)*delta**r for r in range(k-2))
            assert err**(2**(k-2)) <= (delta*t*t)**(2**(k-3))*q
            checks += 1
    counts['higher_AP_rational_quadratic_bounds'] = checks

    rank_one = []
    rank_counts = {0:0,1:0,2:0}
    for t0,t1,t2 in product((-2,-1,1,2), repeat=3):
        a,b,c = t0+t1+t2, t1+2*t2, t1+4*t2
        determinant = a*c-b*b
        assert abs(determinant) <= 24
        rank = 0 if (a%29,b%29,c%29)==(0,0,0) else (1 if determinant%29==0 else 2)
        rank_counts[rank] += 1
        if rank==1:
            rank_one.append([t0,t1,t2])
    assert rank_counts == {0:0,1:2,2:62}
    assert rank_one == [[-1,2,-1],[1,-2,1]]
    counts['quadratic_phase_rank_cases'] = 64

    # Exact pair-quotient averaging in non-coprime cyclic systems.
    checks = 0
    for n in range(2,12):
        for d in range(n):
            f = tuple(rng.choice(alphabet) for _ in range(n))
            g = tuple(rng.choice(alphabet) for _ in range(n))
            h = image(n,d)
            m = gcd(n,d)
            lhs = sum(f[x]*g[(x+d*y)%n] for x in range(n) for y in range(n))/n**2
            rhs = sum((sum(f[x] for x in range(r,n,m))/len(h))*
                      (sum(g[x] for x in range(r,n,m))/len(h)) for r in range(m))/m
            assert lhs == rhs
            checks += 1
    counts['exact_pair_quotient_identities'] = checks

    table = []
    for delta in (.1,.25,.5):
        for k in (3,4,5,8,12):
            sigma = sqrt(delta*(1-delta))
            B = sum((j-1)*delta**(j-2)*min(sqrt(delta),sigma*(1-delta**(k-j))/(1-delta))
                    for j in range(2,k))
            linear = sum(delta**r for r in range(k-2))
            table.append(dict(delta=delta,k=k,B=B,linear_coefficient=linear,
                              threshold_u=sqrt(delta**k/(2*B))))

    report = {'status':'PASS','seed':20261006,'exact_checks':counts,
              'total_exact_checks':sum(counts.values()),'rank_one_triples':rank_one,
              'rank_census':rank_counts,'coefficient_table_floating_point':table,
              'scope':'Finite checks supplement human proofs; no proof-assistant verification.'}
    if args.gauss:
        import numpy as np
        p=29
        n=p*p
        a=1/16
        z=np.indices((p,p))
        Q=(z[0]**2+z[1]**2)%p
        h=sum(a*np.exp(2j*np.pi*t*Q/p) for t in (-2,-1,1,2)).real
        f=h-4*a/np.sqrt(n)
        # Uniform x,y in F_29^2, summed one difference at a time.
        val=0.0
        for y0,y1 in product(range(p),repeat=2):
            val += float(np.mean(f*np.roll(f,(-y0,-y1),(0,1))*np.roll(f,(-2*y0,-2*y1),(0,1))))
        val /= n
        expected=a**3*(2/n**.5+62/n-64/n**1.5)
        U4=float(np.sum(abs(np.fft.fftn(f)/n)**4))
        assert abs(val-expected)<1e-12
        assert U4 <= (4*a)**4/n+1e-14
        report['floating_point_gauss_check']={'status':'PASS','group':'F_29^2',
            'direct_count':val,'exact_formula_evaluated':expected,
            'absolute_discrepancy':abs(val-expected),'U2_fourth_power':U4,
            'U2_fourth_power_upper_bound':(4*a)**4/n}
    Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
