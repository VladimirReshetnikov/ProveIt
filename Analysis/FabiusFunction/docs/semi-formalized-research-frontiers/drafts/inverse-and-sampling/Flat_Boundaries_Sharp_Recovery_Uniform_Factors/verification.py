#!/usr/bin/env python3
"""Reproduce exact algebra and numerical Hellinger diagnostics for the article.

No network access or repository writes.  Numerical quadrature is diagnostic,
not interval-certified.  The all-order theorems are proved in article.tex.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
from pathlib import Path

import mpmath as mp
import sympy as sp


def exact_checks() -> dict:
    t = sp.Symbol('t')
    series = sp.series(sp.log(sp.sinh(t)/t), t, 0, 14).removeO().expand()
    cumulants = []
    for k in range(1, 7):
        c = sp.factor(series.coeff(t, 2*k) * sp.factorial(2*k))
        assert c == sp.Rational(2**(2*k), 2*k)*sp.bernoulli(2*k)
        cumulants.append(str(c))
    rng = random.Random(20260929)
    count = 0
    for m in range(1, 8):
        for shift in range(3):
            for _ in range(100):
                x = sorted(sp.Rational(rng.randrange(33), 32) for i in range(m))
                y = sorted(sp.Rational(rng.randrange(33), 32) for i in range(m))
                h = max(abs(a-b) for a,b in zip(x,y))
                e = max(abs(sum(a**k for a in x)-sum(b**k for b in y))
                        for k in range(shift+1, shift+m+1))
                assert h**(m+shift) <= 8**(m+shift)*e
                count += 1
    tangent_checks = 0
    for m in range(1, 9):
        u = [sp.Rational(i+1, m+2) for i in range(m)]
        pp = [sp.prod(u[i]-u[j] for j in range(m) if j != i) for i in range(m)]
        for shift in (0,1):
            b = [1/(u[i]**shift * pp[i]) for i in range(m)]
            for k in range(shift+1, shift+m):
                assert sum(k*u[i]**(k-1)*b[i] for i in range(m)) == 0
            assert sum((shift+m)*u[i]**(shift+m-1)*b[i] for i in range(m)) == shift+m
            if shift == 1:
                assert sum(b) == (-1)**(m+1)/sp.prod(u)
            tangent_checks += 1
    u = [sp.Rational(1,4),sp.Rational(3,4)]
    w_known = [sp.Rational(1,8),sp.Rational(7,8)]
    w_unknown = [sp.Rational(39,404),sp.Rational(317,404)]
    p = lambda x,k: sum(z**k for z in x)
    assert p(u,1)==p(w_known,1)
    assert p(u,2)==p(w_unknown,2)
    assert p(u,1)/3 == p(w_unknown,1)/3+sp.Rational(4,101)
    delta4 = sp.Rational(-2,15)*(p(u,2)-p(w_known,2))
    delta6 = sp.Rational(16,63)*(p(u,3)-p(w_unknown,3))
    assert delta4 == sp.Rational(1,48)
    constants = {
        'uniform_vs_zero_H2_over_h4_J2': sp.Rational(1,3)**2/(4*sp.factorial(2)**2),
        'uniform_vs_variance_matched_Gaussian_H2_over_h8_J4': sp.Rational(-2,15)**2/(4*sp.factorial(4)**2),
        'four_uniform_buffer_log_constant': sp.Rational(1,96)*sp.Rational(1,3)**2*sp.binomial(3,2)**2/2,
        'eight_uniform_buffer_log_constant': sp.Rational(1,1290240)*sp.Rational(-2,15)**2*sp.binomial(7,4)**2/2,
        'two_factor_known_delta4': delta4,
        'two_factor_known_H_constant_divided_by_J4': delta4**2/(4*sp.factorial(4)**2),
        'two_factor_unknown_delta6': delta6,
        'two_factor_unknown_H_constant_divided_by_J6': delta6**2/(4*sp.factorial(6)**2),
    }
    assert constants['four_uniform_buffer_log_constant'] == sp.Rational(1,192)
    assert constants['eight_uniform_buffer_log_constant'] == sp.Rational(7,829440)
    return {'status':'passed', 'seed':20260929, 'rational_inverse_inequality_checks':count,
            'tangent_checks':tangent_checks, 'uniform_cumulants':cumulants,
            'constants':{k:str(sp.factor(v)) for k,v in constants.items()},
            'unknown_pair':{'u':[str(z) for z in u], 'w':[str(z) for z in w_unknown],
                            'variance_coefficients':['0','4/101']}}


def spline(m: int, x: mp.mpf, derivative: int = 0) -> mp.mpf:
    """Density of a sum of m Unif[-1,1], or its derivative off knots."""
    if not 0 <= derivative < m:
        raise ValueError('Require 0 <= derivative < m.')
    if abs(x) >= m:
        return mp.mpf('0')
    sign = 1
    if x > 0:
        x = -x
        sign = (-1)**derivative
    power = m-1-derivative
    acc = mp.mpf('0')
    for k in range(m+1):
        z = x+m-2*k
        if z > 0:
            acc += (-1)**k * math.comb(m,k)*z**power
    return sign*acc/(2**m*math.factorial(power))


def spline_uniform(m: int, h: mp.mpf, x: mp.mpf) -> mp.mpf:
    if abs(x) >= m+h:
        return mp.mpf('0')
    x = -abs(x)
    acc = mp.mpf('0')
    for k in range(m+1):
        z = x+m-2*k
        acc += (-1)**k * math.comb(m,k)*(max(z+h,0)**m-max(z-h,0)**m)
    value = acc/(2*h*2**m*math.factorial(m))
    if value < 0:
        if abs(value) > mp.mpf('1e-40'):
            raise ArithmeticError(f'Unexpected negative density {value}')
        return mp.mpf('0')
    return value


def hellinger_uniform(m: int, h: mp.mpf) -> mp.mpf:
    knots = {mp.mpf(0), mp.mpf(m), mp.mpf(m)+h}
    for k in range(m+1):
        base = mp.mpf(-m+2*k)
        for shift in (-h,mp.mpf(0),h):
            q = base+shift
            if 0 < q < m+h:
                knots.add(q)
    cuts = sorted(knots)
    def integrand(x: mp.mpf) -> mp.mpf:
        p = spline(m,x)
        q = spline_uniform(m,h,x)
        # Stable evaluation of the squared square-root difference.
        if p+q == 0:
            return mp.mpf('0')
        return (p-q)**2/(mp.sqrt(p)+mp.sqrt(q))**2
    return 2*sum(mp.quad(integrand,[a,b]) for a,b in zip(cuts,cuts[1:]))


def information(m: int, r: int) -> mp.mpf:
    if m <= 2*r:
        raise ValueError('The finite integral requires m > 2*r here.')
    def integrand(x: mp.mpf) -> mp.mpf:
        p = spline(m,x)
        if p == 0:
            return mp.mpf('0')
        return spline(m,x,r)**2/p
    cuts = sorted({mp.mpf(0),mp.mpf(m)} | {mp.mpf(-m+2*k) for k in range(m+1) if 0 < -m+2*k < m})
    return 2*sum(mp.quad(integrand,[a,b]) for a,b in zip(cuts,cuts[1:]))


def numerical_checks(out: Path, dps: int) -> dict:
    mp.mp.dps = dps
    c1 = 2*(mp.sqrt(2)-1)/3
    j2 = information(5,2)
    c5 = j2/144
    def profile_difference_sq(t: mp.mpf) -> mp.mpf:
        a = (max(1-t,0)**3-max(-1-t,0)**3)/6
        b = max(-t,0)**2
        if a+b == 0:
            return mp.mpf(0)
        return (a-b)**2/(mp.sqrt(a)+mp.sqrt(b))**2
    # t=-u, u>1: a=u^2+1/3, b=u^2; stable infinite tail.
    tail = mp.quad(lambda u: (mp.mpf(1)/3)**2/(mp.sqrt(u*u+mp.mpf(1)/3)+u)**2,[1,mp.inf])
    a3 = tail + mp.quad(profile_difference_sq,[-1,0,1])
    c3 = a3/8  # 2*C_3=1/8.
    rows = []
    previous4 = None
    for m in (1,3,4,5):
        for j in (3,4,5,6,7):
            h = mp.mpf(2)**(-j)
            h2 = hellinger_uniform(m,h)
            power = min(m,4)
            normalized = h2/h**power
            target = {1:c1,3:c3,4:mp.mpf(1)/192,5:c5}[m]
            if m == 4:
                ratio = normalized/mp.log(1/h)
                slope = '' if previous4 is None else mp.nstr((normalized-previous4)/mp.log(2),24)
                previous4 = normalized
            else:
                ratio = normalized
                slope = ''
            if m == 1:
                assert abs(ratio-c1) < mp.mpf('1e-35')
            rows.append({'M':m, 'h':str(h), 'H_squared':mp.nstr(h2,24),
                         'normalized':mp.nstr(ratio,24), 'target':mp.nstr(target,24),
                         'critical_log_slope':slope})
    with (out/'data'/'hellinger_diagnostics.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    return {'status':'completed', 'decimal_precision':dps, 'rows':len(rows),
            'J2_five_uniform_buffer':mp.nstr(j2,40),
            'H_regular_constant_M5':mp.nstr(c5,40),
            'profile_integral_A3':mp.nstr(a3,40),
            'H_boundary_constant_M3':mp.nstr(c3,40),
            'one_uniform_exact_constant':mp.nstr(c1,40),
            'note':'High-precision numerical quadrature, not interval-certified; no numerical up-density information integral is claimed.'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--dps',type=int,default=60)
    args=parser.parse_args()
    if args.dps < 45:
        parser.error('--dps must be at least 45')
    out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True);(out/'data').mkdir(exist_ok=True)
    result={'exact':exact_checks(), 'versions':{'sympy':sp.__version__,'mpmath':mp.__version__}}
    print('Exact checks passed.',flush=True)
    if not args.exact_only:
        result['numerical']=numerical_checks(out,args.dps)
        print('Numerical Hellinger diagnostics completed.',flush=True)
    (out/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
