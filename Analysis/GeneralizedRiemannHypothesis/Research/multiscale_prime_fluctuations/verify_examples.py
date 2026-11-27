#!/usr/bin/env python3
"""Exact rational probe checks and illustrative, non-certified zeta numerics.
Requires numpy and mpmath; run from any directory. Results go beside script.
"""
from fractions import Fraction
from math import gcd, isqrt, log, sqrt, pi
import csv
from pathlib import Path
import numpy as np
import mpmath as mp

HERE = Path(__file__).resolve().parent

def save(name, header, rows):
    with (HERE / name).open('w', newline='') as f:
        w = csv.writer(f); w.writerow(header); w.writerows(rows)

def factors(n):
    assert n >= 1
    out, d = [], 2
    while d*d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out

def probe_example():
    q = 12
    scales = list(map(Fraction, [1, 2, '3/2', 5]))
    primes = {1: 13, 5: 17, 7: 19, 11: 11}
    assert set(primes) == {a for a in range(q) if gcd(a, q) == 1}
    rows = []
    for a, p in primes.items():
        assert p % q == a and factors(p) == [p]
        for j, sj in enumerate(scales):
            for k, sk in enumerate(scales):
                u = p * sk / sj
                assert u >= 2
                is_pp = u.denominator == 1 and len(factors(u.numerator)) == 1
                assert is_pp == (j == k)
                rows.append((a, p, str(sj), str(sk), str(u), is_pp))
    save('prime_probes.csv', ['residue_mod_12','probe_prime','scale_j','scale_k','argument','is_prime_power'], rows)
    print(f'Exact rational probe checks: {len(rows)} passed; {sum(r[-1] for r in rows)} diagonal arguments.', flush=True)

def mangoldt_prefix(nmax):
    sieve = np.ones(nmax+1, dtype=bool); sieve[:2] = False
    for p in range(2, isqrt(nmax)+1):
        if sieve[p]: sieve[p*p::p] = False
    lam = np.zeros(nmax+1, dtype=float)
    for p0 in np.flatnonzero(sieve):
        p = int(p0); pk = p
        while pk <= nmax:
            lam[pk] = log(p); pk *= p
    weighted = np.zeros_like(lam)
    weighted[1:] = lam[1:] / np.arange(1,nmax+1,dtype=float)
    return np.cumsum(lam), np.cumsum(weighted)

def zeta_example():
    mp.mp.dps = 25
    zeros = np.array([float(mp.im(mp.zetazero(n))) for n in range(1,61)])
    save('zeta_ordinates.csv',['index','approx_positive_ordinate'],enumerate(zeros,1))
    den = .25 + zeros**2
    points = [1000,3000,10000,30000,100000,300000,1000000]
    psi, weighted = mangoldt_prefix(max(points))
    rows = []
    print('\nZeta-only check (truncated spectral approximation):')
    for x in points:
        actual = sqrt(x)*(weighted[x]-psi[x]/x-log(x)+1+float(mp.euler))
        spectral = float(2*np.sum(np.cos(zeros*log(x))/den))
        # z=-1 residue, not a critical-line zero. Other trivial zero terms
        # have total normalized magnitude <= x^(-5/2)/(6*(1-x**(-2))).
        corrected = spectral + log(2*pi)/sqrt(x)
        error = actual-corrected
        rows.append((x,actual,spectral,corrected,error))
        print(f'x={x:7d} direct={actual:+.10f} corrected={corrected:+.10f} diff={error:+.3e}')
    save('zeta_ramp_examples.csv',['x','direct_normalized_remainder','truncated_zero_series','plus_z_minus_1_correction','direct_minus_approx'],rows)
    shifts = np.log([1.,2.,3.]); results=[]
    print('\nFinite real covariance matrices from selected zeta ordinates:')
    for lo, hi in [(0,60),(20,40),(40,60)]:
        z = np.exp(1j*zeros[lo:hi,None]*shifts[None,:])/den[lo:hi,None]
        Q = 2*np.real(z.T @ z.conj()); eig = np.linalg.eigvalsh(Q)
        assert eig[0]>0
        print(f'zeros {lo+1}..{hi}, eigenvalues = {eig}, condition = {eig[-1]/eig[0]:.6g}')
        for i in range(3):
            for j in range(3): results.append((lo+1,hi,i,j,Q[i,j]))
    save('zeta_covariances.csv',['first_zero','last_zero','row','column','covariance'],results)
    print('\nNumerical examples only; no rigorous zero enclosures or asymptotic constants.')

if __name__ == '__main__':
    probe_example(); zeta_example()
