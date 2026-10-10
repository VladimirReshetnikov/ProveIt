#!/usr/bin/env python3
"""Exact certificates for compensated polylogarithms (standard library only).

All interval endpoints are rational. Integer roots are checked by inequalities;
no floating-point evaluation is used in any acceptance test. The mathematical
remainder estimates are proved in article.tex; this script replays finite tests,
not a proof-assistant formalization of the analytic theorems.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIGITS = 80
SCALE = 10 ** DIGITS
ROOT_CHECKS = 0


def ceildiv(n: int, d: int) -> int:
    assert d > 0
    return -((-n) // d)


def iroot(n: int, q: int) -> int:
    """Floor qth root, verified independently after Newton iteration."""
    if n < 0 or q < 1:
        raise ValueError("iroot needs n >= 0, q >= 1")
    if n < 2 or q == 1:
        return n
    r = 1 << ceildiv(n.bit_length(), q)
    while True:
        t = ((q - 1) * r + n // (r ** (q - 1))) // q
        if t >= r:
            break
        r = t
    while r ** q > n:
        r -= 1
    while (r + 1) ** q <= n:
        r += 1
    assert r ** q <= n < (r + 1) ** q
    return r


@lru_cache(maxsize=None)
def power_interval(n: int, exponent: F) -> tuple[int, int]:
    """Endpoints on SCALE^-1 Z for n^(-exponent)."""
    global ROOT_CHECKS
    if n < 1 or exponent <= 0:
        raise ValueError("positive integer base and positive exponent required")
    p, q = exponent.numerator, exponent.denominator
    target = n ** p * SCALE ** q
    r = iroot(target, q)
    assert r ** q <= target < (r + 1) ** q
    ROOT_CHECKS += 1
    if r ** q == target:
        return SCALE * SCALE // r, ceildiv(SCALE * SCALE, r)
    return SCALE * SCALE // (r + 1), ceildiv(SCALE * SCALE, r)


def coefficients(a: F, b: F, nmax: int) -> list[tuple[int, int]]:
    """c[n] encloses H_(n-1)^(b)/n^a, with c[0]=c[1]=0."""
    result = [(0, 0)] * (nmax + 1)
    hlo = hhi = 0
    for n in range(1, nmax + 1):
        plo, phi = power_interval(n, a)
        result[n] = (hlo * plo // SCALE, ceildiv(hhi * phi, SCALE))
        blo, bhi = power_interval(n, b)
        hlo, hhi = hlo + blo, hhi + bhi
    return result


def outward_decimal(x: F, places: int, upper: bool = False) -> str:
    unit = 10 ** places
    k = ceildiv(x.numerator * unit, x.denominator) if upper else x.numerator * unit // x.denominator
    sign = '-' if k < 0 else ''
    k = abs(k)
    return f"{sign}{k // unit}.{k % unit:0{places}d}"


def record_interval(lo: F, hi: F, places: int = 62) -> dict:
    assert lo <= hi
    return {
        'lower': {'numerator': str(lo.numerator), 'denominator': str(lo.denominator)},
        'upper': {'numerator': str(hi.numerator), 'denominator': str(hi.denominator)},
        'decimal_lower': outward_decimal(lo, places),
        'decimal_upper': outward_decimal(hi, places, True),
        'width_upper': outward_decimal(hi-lo, 75, True),
    }


def euler_enclosure(a: F, b: F, nterms: int = 192) -> tuple[F, F]:
    c = coefficients(a, b, 2 * nterms - 1)
    # coefficient of (-1)^n c_(2n+1) is a binomial tail / 2^N.
    tail = (1 << nterms) - 1
    numerator_lo = numerator_hi = 0
    for n in range(nterms):
        lo, hi = c[2*n+1]
        if n % 2:
            numerator_lo -= tail * hi
            numerator_hi -= tail * lo
        else:
            numerator_lo += tail * lo
            numerator_hi += tail * hi
        tail -= comb(nterms, n+1)
    assert tail == 0
    den = SCALE * (1 << nterms)
    elo, ehi = F(numerator_lo, den), F(numerator_hi, den)
    # Universal all-positive-order bound H_2^(b) < 2.
    return elo - F(2, 1 << nterms), ehi


def angular_enclosure(cn: list[tuple[int,int]], rho: F, cosine: F) -> tuple[F, F]:
    """Exact Chebyshev evaluation with outward rounding of each rational term.

    U_j(P/Q) = V_j/Q^j, V_j = 2P V_(j-1) - Q^2 V_(j-2).
    This avoids interval-recursion blowup and arbitrary-precision trig functions.
    """
    if not (0 < rho < 1 and -1 < cosine < 1):
        raise ValueError("interior radius and cosine required")
    P, Q = cosine.numerator, cosine.denominator
    R, S = rho.numerator, rho.denominator
    vprev, vcur = 0, 1
    qpow, rpow, spow = 1, R, S
    lower = upper = 0
    N = len(cn)-1
    for n in range(1, N+1):
        scalar_num = rpow * vcur
        scalar_den = spow * qpow
        cl, ch = cn[n]
        if scalar_num >= 0:
            lower += cl * scalar_num // scalar_den
            upper += ceildiv(ch * scalar_num, scalar_den)
        else:
            lower += ch * scalar_num // scalar_den
            upper += ceildiv(cl * scalar_num, scalar_den)
        vprev, vcur = vcur, 2*P*vcur-Q*Q*vprev
        qpow *= Q
        rpow *= R
        spow *= S
    j = N+1
    rem = rho**j * (F(j*j)/(1-rho) + 2*j*rho/(1-rho)**2 + rho*(1+rho)/(1-rho)**3)
    return F(lower,SCALE)-rem, F(upper,SCALE)+rem


def strict_coefficient(indices: tuple[int, ...], n: int) -> F:
    """Finite exact decreasing-index coefficient, at integer orders."""
    if len(indices) == 1:
        return F(1, n**indices[0])
    return sum((strict_coefficient(indices[1:], m) for m in range(1,n)), F(0)) / n**indices[0]


def det(matrix: list[list[F]]) -> F:
    a = [r[:] for r in matrix]
    value = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j,len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j],a[pivot] = a[pivot],a[j]
            value = -value
        p = a[j][j]
        value *= p
        for i in range(j+1,len(a)):
            m = a[i][j]/p
            for k in range(j+1,len(a)):
                a[i][k] -= m*a[j][k]
    return value


def exact_moment_checks() -> dict:
    differences = hankels = 0
    examples = [(1,), (2,), (1,1), (2,1), (1,2), (1,1,1), (2,1,1), (1,1,1,1)]
    for s in examples:
        d = len(s)
        moments = [strict_coefficient(s,n+d)/comb(n+d-1,d-1) for n in range(13)]
        row = moments
        while row:
            assert all(x > 0 for x in row)
            differences += len(row)
            row = [row[j]-row[j+1] for j in range(len(row)-1)]
        for size in range(1,5):
            for shift in range(3):
                h = [[moments[i+j+shift] for j in range(size)] for i in range(size)]
                assert det(h) > 0
                hankels += 1
    bad = [strict_coefficient((1,1),n+2) for n in range(3)]
    witness = bad[0]-2*bad[1]+bad[2]
    assert witness == -F(1,24)
    return {'positive_finite_differences': differences, 'positive_hankel_determinants': hankels,
            'depths_tested': [1,2,3,4], 'alpha_1_depth_2_counterexample': str(witness)}


def affine_difference_checks() -> int:
    checks = 0
    for a in [1, 2]:
        for b in [1, 3]:
            for r in [1, 2, 3]:
                bound = sum((F(1, j**b) for j in range(1, r+1)), F(0))
                for step in [F(1,2), F(1), F(3)]:
                    vals = [sum((F(1, j**b) for j in range(1, r*n+1)), F(0))
                            / (step*n+1)**a for n in range(9)]
                    assert vals[0] == 0
                    for k in range(1, 9):
                        dk = sum(((-1)**n*comb(k,n)*vals[n] for n in range(k+1)), F(0))
                        assert 0 < -dk < bound
                        checks += 1
    return checks


def run() -> dict:
    pairs = [('1/10','1/10'),('1/4','1/4'),('2/5','1/5'),('1/3','1/3'),
             ('1/10','9/10'),('1/2','1/2'),('9/10','1/10'),('1','1'),('2','3')]
    vals=[]
    for aa,bb in pairs:
        lo,hi=euler_enclosure(F(aa),F(bb))
        assert hi < 0 and hi-lo < F(1,10**55)
        vals.append({'a':aa,'b':bb,'N':192,'tail_constant':2,**record_interval(lo,hi)})
    props=json.loads((ROOT/'data/angular_proposals.json').read_text())
    brackets=[]
    cache={}
    for p in props:
        key=(p['a'],p['b'])
        if key not in cache:
            cache[key]=coefficients(F(key[0]),F(key[1]),400)
        rho,cl,ch=F(p['rho']),F(p['cosine_lower']),F(p['cosine_upper'])
        _,neg_upper=angular_enclosure(cache[key],rho,cl)
        pos_lower,_=angular_enclosure(cache[key],rho,ch)
        assert neg_upper < 0 < pos_lower, (p,neg_upper,pos_lower)
        assert rho/2 < cl < ch < rho
        brackets.append({**p,'terms':400,'negative_endpoint_upper':str(neg_upper),
                         'positive_endpoint_lower':str(pos_lower),'status':'exact sign bracket'})
    return {'arithmetic':'integers and fractions; no floating-point acceptance',
            'decimal_grid_digits':DIGITS,'integer_root_inequalities_checked':ROOT_CHECKS,
            'gaussian_enclosures':vals,'angular_brackets':brackets,'moment_checks':exact_moment_checks(),
            'affine_difference_checks':affine_difference_checks()}


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run this verifier without -O; assertions must be enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='compare recomputed results to the frozen JSON')
    args=parser.parse_args()
    output=run()
    path=ROOT/'data/exact_certificates.json'
    if args.check:
        assert json.loads(path.read_text())==output, 'frozen certificate differs from replay'
        print('PASS: exact replay equals the frozen certificate.')
    else:
        path.write_text(json.dumps(output,indent=2)+'\n')
    print(f"PASS: {len(output['gaussian_enclosures'])} Euler enclosures; "
          f"{len(output['angular_brackets'])} angular brackets; "
          f"{output['integer_root_inequalities_checked']} checked roots.")
    print(output['moment_checks'])

