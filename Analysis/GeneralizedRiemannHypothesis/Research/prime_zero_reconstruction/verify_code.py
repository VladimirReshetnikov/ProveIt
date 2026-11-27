#!/usr/bin/env python3
"""Reproducible tests of the universal coefficient code and finite Fourier model.

No third-party packages; exact integers/Fractions for the algebraic checks.
The last test uses complex floating point for a synthetic spectrum only.
This is not a Lean check or a computation of actual L-function zeros.
"""
from fractions import Fraction as Q
from itertools import product
from math import isqrt
import cmath


def primes():
    p = 2
    while True:
        if all(p % k for k in range(2, isqrt(p) + 1)):
            yield p
        p += 1


def ceil_log2_ratio(a):
    """Least nonnegative k for 2**k >= positive rational a."""
    if a <= 1:
        return 0
    k = max(0, a.numerator.bit_length() - a.denominator.bit_length())
    while Q(1 << k) < a:
        k += 1
    while k and Q(1 << (k-1)) >= a:
        k -= 1
    return k


def make_code(conductors):
    """Return radicals p, exponents k, exact separation d (paper, Eq. 4-5)."""
    assert conductors[0] == 1
    w = [q + 1 for q in conductors]
    ps = [1] + [p for _, p in zip(range(1, len(w)), primes())]
    ks, ds = [0], [Q(1)]
    for j in range(1, len(w)):
        bound = min([Q(1)] + [ds[n] / (n+1) for n in range(j)]) / (1 << (j+2))
        k = ceil_log2_ratio(Q(ps[j] * w[j]) / bound)
        ks.append(k)
        D = 1 << max(ks)
        ds.append(Q(1, D * (3 * D * (j+1))**((1 << j)-1)))
        assert Q(ps[j] * w[j], 1 << k) <= bound
        if k:
            assert Q(ps[j] * w[j], 1 << (k-1)) > bound
    for n, d in enumerate(ds):
        # Using p_j rather than sqrt(p_j) gives a rigorous upper bound.
        finite_tail = sum((Q(ps[j]*w[j], 1 << ks[j])
                           for j in range(n+1, len(w))), Q(0))
        assert finite_tail <= d / ((n+1)*(1 << (n+2)))
    return w, ps, ks, ds


def scaled_radical_floor(p, k, bits):
    """Exact floor of 2**bits * sqrt(p)/2**k, without floating point."""
    if bits >= k:
        return isqrt(p << (2*(bits-k)))
    return isqrt(p) >> (k-bits)


def interval_for(v, ps, ks, bits):
    """Dyadic enclosure for a nonnegative integer linear combination."""
    lo = sum(m * scaled_radical_floor(p, k, bits)
             for m, p, k in zip(v, ps, ks))
    # Each nonintegral radical floor loses <1 unit. c0 is exact.
    hi = lo + sum(v[1:])
    return Q(lo, 1 << bits), Q(hi, 1 << bits)


def prefix_check(w, ps, ks, ds, n, m):
    d = ds[n]
    assert len(m) == len(w)
    assert all(0 <= mj <= (n+1)*wj for mj, wj in zip(m,w))
    bits = d.denominator.bit_length() + 20
    alo, ahi = interval_for(m, ps, ks, bits)
    assert ahi-alo < d/8
    estimate = (alo + ahi)/2
    # Exhaust all prefixes; candidate inclusion/exclusion is certified by intervals.
    floors = [scaled_radical_floor(p,k,bits) for p,k in zip(ps[:n+1],ks[:n+1])]
    scale = 1 << bits
    # Enumerate using scaled integers, so no cancellation or roundoff.
    threshold = d/2
    matches = []
    boundary_uncertain = 0
    all_floors = []
    for v in product(*(range((n+1)*wj+1) for wj in w[:n+1])):
        low = sum(vj*f for vj,f in zip(v,floors))
        high = low + sum(v[1:])
        all_floors.append(low)
        lo,hi = Q(low,scale),Q(high,scale)
        if lo > estimate-threshold and hi < estimate+threshold:
            matches.append(v)
        elif not (hi <= estimate-threshold or lo >= estimate+threshold):
            boundary_uncertain += 1
    assert matches == [tuple(m[:n+1])]
    assert boundary_uncertain == 0
    all_floors.sort()
    # A deliberately conservative certified lower bound for every adjacent separation.
    max_uncertainty = sum((n+1)*wj for wj in w[1:n+1])
    min_gap = min(b-a for a,b in zip(all_floors, all_floors[1:]))
    assert Q(min_gap-max_uncertainty,scale) >= d
    print(f'  prefix 0..{n}: {len(all_floors):,} candidates; unique recovery {matches[0]}; exact gap check PASS')


def finite_fourier_demo():
    """A synthetic signal with common ordinates, central and negative frequencies."""
    # Modest positive weights for a visible numerical example, not universal weights.
    weights = [1.0, 0.31, 0.19]
    multiplicities = {-4.0: (0,1,2), 0.0:(2,1,1), 1.75:(1,3,0), 2.6:(0,1,1)}
    a = {}
    for gamma, m in multiplicities.items():
        rho = .5 + 1j*gamma
        A = sum(c*j for c,j in zip(weights,m))
        a[gamma] = -A/(rho*(rho+1))
    def mean_exp(freq, T):
        return 1 if freq == 0 else (cmath.exp(1j*freq*T)-1)/(1j*freq*T)
    def C_T(h,T):
        return sum(x*y.conjugate()*cmath.exp(1j*g*h)*mean_exp(g-k,T)
                   for g,x in a.items() for k,y in a.items())
    def C(h):
        return sum(abs(x)**2*cmath.exp(1j*g*h) for g,x in a.items())
    for T in (100, 10000, 1000000):
        error = max(abs(C_T(h,T)-C(h)) for h in (-1,0,0.7,3.0))
        B = sum(map(abs,a.values()))
        gap = min(abs(g-k) for g in a for k in a if g != k)
        assert error <= 2*B*B/(T*gap)+1e-12
        print(f'  synthetic first mean T={T:>7}: max error={error:.3e}')
    U = 10000000
    for gamma, m in multiplicities.items():
        power = sum(abs(x)**2*mean_exp(g-gamma,U) for g,x in a.items())
        rho = .5+1j*gamma
        recovered = abs(rho*(rho+1))*abs(power.real)**.5
        expected = sum(c*j for c,j in zip(weights,m))
        assert abs(recovered-expected) < 1e-4
    print('  synthetic second mean: recovered aggregate multiplicities at every frequency PASS')


def main():
    # Conductors of the first five primitive characters, ordering within 5 arbitrary.
    q = [1,3,4,5,5]
    w, ps, ks, ds = make_code(q)
    print('Exact rational recursion and finite weighted-tail certificates: PASS')
    print('  j   q_j  p_j   k_j    separation denominator bits')
    for j in range(len(q)):
        print(f'  {j}   {q[j]:>3}  {ps[j]:>3}  {ks[j]:>5}   {ds[j].denominator.bit_length():>6}')
    # Multiple characters contribute at the same synthetic frequency, plus a tail.
    prefix_check(w,ps,ks,ds,2,[2,3,1,4,2])
    prefix_check(w,ps,ks,ds,3,[0,2,5,1,4])
    finite_fourier_demo()
    print('All tests passed. Analytic results are proved in reconstruction.tex, not by these tests.')

if __name__ == '__main__':
    main()
