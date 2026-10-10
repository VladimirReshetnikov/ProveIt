#!/usr/bin/env python3
"""Exact rational certificates for real-order harmonic polylogarithms.

Only Python's standard library is used. Rational powers are enclosed by
integer nth-root inequalities, not floating-point approximations. Analytic
remainder bounds are proved in the companion article.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from math import comb
from pathlib import Path
from typing import TypeAlias

if not __debug__:
    raise RuntimeError("Run this exact verifier without Python -O; proof checks use assertions.")

Interval: TypeAlias = tuple[Q, Q]
ROOT_CHECKS = 0
GRID = 10**60

def outward(x: Interval) -> Interval:
    """Outward rounding using integer division only; keeps arithmetic small."""
    lo, hi = x
    lower = (lo.numerator*GRID)//lo.denominator
    upper = -((-hi.numerator*GRID)//hi.denominator)
    return Q(lower, GRID), Q(upper, GRID)

def add(x: Interval, y: Interval) -> Interval:
    return outward((x[0] + y[0], x[1] + y[1]))

def scale(x: Interval, q: Q) -> Interval:
    return outward((x[0]*q, x[1]*q) if q >= 0 else (x[1]*q, x[0]*q))

def mul_positive(x: Interval, y: Interval) -> Interval:
    assert x[0] >= 0 and y[0] >= 0
    return outward((x[0]*y[0], x[1]*y[1]))

def integer_root(n: int, k: int) -> int:
    """Return floor(n**(1/k)) with an explicit integer proof check."""
    global ROOT_CHECKS
    if n < 0 or k < 1:
        raise ValueError('n must be nonnegative and k positive')
    if n <= 1 or k == 1:
        x = n
    else:
        x = 1 << ((n.bit_length() + k - 1)//k)
        while True:
            y = ((k-1)*x + n//pow(x, k-1))//k
            if y >= x:
                break
            x = y
        while pow(x, k) > n:
            x -= 1
        while pow(x+1, k) <= n:
            x += 1
    assert pow(x, k) <= n < pow(x+1, k)
    ROOT_CHECKS += 1
    return x

def inverse_power(n: int, exponent: Q, digits: int = 65) -> Interval:
    if n < 1 or exponent <= 0:
        raise ValueError('positive n and exponent required')
    p, q = exponent.numerator, exponent.denominator
    if q == 1:
        value = Q(1, n**p)
        return value, value
    B = 10**digits
    radicand = n**p * B**q
    r = integer_root(radicand, q)
    if r**q == radicand:
        value = Q(B, r)
        return value, value
    return Q(B, r+1), Q(B, r)

def moments(a: Q, b: Q, N: int, digits: int = 65) -> list[Interval]:
    """c[n] encloses H_(n-1)^(b)/n^a, 1 <= n <= N."""
    if a <= 0 or b <= 0 or N < 1:
        raise ValueError('positive parameters and N required')
    out: list[Interval] = [(Q(0), Q(0))]
    harmonic = (Q(0), Q(0))
    for n in range(1, N+1):
        out.append(mul_positive(harmonic, inverse_power(n, a, digits)))
        harmonic = add(harmonic, inverse_power(n, b, digits))
    return out

def mass_bound(a: Q, b: Q) -> Q:
    if a+b < 1:
        raise ValueError('the signed-measure certificate requires a+b >= 1')
    if a >= 1:
        return Q(1)  # prior angular-continuation theorem, rederived in article
    if b < 1:
        return 1/(1-b)
    if b > 1:
        return b/(b-1)  # zeta(b) < 1 + 1/(b-1)
    return 1 + 1/a     # translation bound: m <= zeta(a+1) < 1+1/a

def euler_interval(a: Q, b: Q, N: int, digits: int = 65) -> tuple[Interval, Interval]:
    cs = moments(a, b, 2*N-1, digits)
    tail = 2**N - 1
    value: Interval = (Q(0), Q(0))
    for n in range(N):
        value = add(value, scale(cs[2*n+1], Q((-1)**n * tail, 2**N)))
        if n+1 < N:
            tail -= comb(N, n+1)
    error = mass_bound(a, b)/2**N
    return value, (value[0]-error, value[1])

def angle_interval(cs: list[Interval], rho: Q, c: Q) -> Interval:
    """Enclose Im F(rho exp(i theta))/sin(theta), cos(theta)=c."""
    if not 0 < rho < 1 or not -1 < c < 1:
        raise ValueError('need 0<rho<1 and -1<c<1')
    N = len(cs)-1
    value: Interval = (Q(0), Q(0))
    prev, current = Q(0), Q(1)  # U_-1, U_0
    rp = rho
    for n in range(1, N+1):
        value = add(value, scale(cs[n], rp*current))
        prev, current = current, 2*c*current-prev
        rp *= rho
    # c_n <= n, |U_(n-1)(c)| <= n.
    r = rho
    j = N+1
    tail = r**j * (Q(j*j)/(1-r) + 2*j*r/(1-r)**2 + r*(1+r)/(1-r)**3)
    return value[0]-tail, value[1]+tail

def decimal_bound(x: Q, places: int, upper: bool = False) -> str:
    scale10 = 10**places
    n = x.numerator*scale10
    v = -((-n)//x.denominator) if upper else n//x.denominator
    sign = '-' if v < 0 else ''
    v = abs(v)
    return f'{sign}{v//scale10}.{v%scale10:0{places}d}'

def interval_json(x: Interval, places: int = 28) -> dict:
    return {'lower': decimal_bound(x[0], places),
            'upper': decimal_bound(x[1], places, True),
            'width_less_than': decimal_bound(x[1]-x[0], places, True)}

def run(output: Path, proposals: Path | None) -> dict:
    global ROOT_CHECKS
    ROOT_CHECKS = 0
    data: dict = {'arithmetic': 'Python int and fractions.Fraction only',
                  'root_rounding_digits': 65, 'outward_grid_digits': 60, 'euler': [], 'angle_brackets': []}
    for a,b in [(Q(1,10),Q(9,10)), (Q(1,10),Q(1)), (Q(1,2),Q(1,2)),
                (Q(3,4),Q(1,2)), (Q(1,2),Q(1)),
                (Q(1,4),Q(3,2)), (Q(1),Q(1)), (Q(2),Q(3))]:
        E,g = euler_interval(a,b,96)
        entry = {'a':str(a), 'b':str(b), 'N':96,
                 'signed_mass_bound':str(mass_bound(a,b)),
                 'E_N':interval_json(E), 'g':interval_json(g)}
        assert g[1] < 0
        if a==Q(1,10) and b in (Q(9,10), Q(1)):
            assert g[1] < Q(-52,100)
            entry['exact_counterexample_check'] = 'g < -13/25 < -1/2; constant-one extension fails at N=1'
            entry['boundary_interpretation'] = 'ordinary convergence' if a+b>1 else 'analytic/Abel value'
        data['euler'].append(entry)
    if proposals:
        proposed = json.loads(proposals.read_text())
        for p in proposed:
            a,b,rho = Q(p['a']),Q(p['b']),Q(p['rho'])
            lo,hi = Q(p['c_lower']),Q(p['c_upper'])
            N = int(p.get('N',200))
            cs=moments(a,b,N)
            left=angle_interval(cs,rho,lo)
            right=angle_interval(cs,rho,hi)
            assert left[1] < 0 < right[0], (p, left, right)
            data['angle_brackets'].append({**p,
               'lower_sign_interval':interval_json(left,32),
               'upper_sign_interval':interval_json(right,32),
               'conclusion':('unique angular zero bracket, by the analytic theorem'
                             if a+b >= 1 else 'at least one angular zero; no uniqueness assertion')})
    data['integer_root_inequalities_checked']=ROOT_CHECKS
    data['all_checks_passed']=True
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(data,indent=2)+'\n')
    return data

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data/exact_certificates.json')
    parser.add_argument('--proposals',type=Path,default=Path(__file__).resolve().parents[1]/'data/root_proposals.json')
    args=parser.parse_args()
    result=run(args.output,args.proposals if args.proposals.exists() else None)
    print(json.dumps({'all_checks_passed':result['all_checks_passed'],
                      'root_inequalities':result['integer_root_inequalities_checked'],
                      'Euler_cases':len(result['euler']),
                      'angular_brackets':len(result['angle_brackets'])},indent=2))
