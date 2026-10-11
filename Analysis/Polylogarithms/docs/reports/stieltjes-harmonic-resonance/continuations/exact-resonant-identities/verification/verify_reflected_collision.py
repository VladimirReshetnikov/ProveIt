#!/usr/bin/env python3
"""Independent local-series/quadrature diagnostics for reflected collisions.

The numerical integral is computed from ordinary quadrature on [b,1-b]
and termwise integrals of convergent endpoint Laurent-log series.
The spectral prediction uses a finite coefficient formula. These are
floating-point diagnostics, not interval certificates.
"""
import argparse
from functools import lru_cache
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def conv(a, b, n):
    return [sum(a[i]*b[k-i] for i in range(k+1)
                if i < len(a) and k-i < len(b)) for k in range(n+1)]


@lru_cache(None)
def rising_coeff(p):
    c = [1]
    for j in range(1, p+1):
        d = [0] * (len(c)+1)
        for i, v in enumerate(c):
            d[i] += j*v
            d[i+1] += v
        c = d
    return c


@lru_cache(None)
def zjet(s, m):
    return mp.diff(mp.zeta, s, m) / mp.factorial(m)


def prediction(m, p, r):
    N = p+r
    if N == 0:
        result = mp.mpf('0')
        for k in range(1, (m+1)//2+1):
            result += (4*mp.factorial(m)*(1-mp.power(2, -2*k))
                       *mp.zeta(2*k)*mp.stieltjes(m-2*k+1)
                       /mp.factorial(m-2*k+1))
        if m % 2 == 0:
            result -= (4*mp.factorial(m)*(1-mp.power(2, -m-2))
                       *mp.zeta(m+2))
        return result
    H = conv(rising_coeff(N), [zjet(N+1, j) for j in range(m+2)], m+1)
    c = mp.mpf('0')
    if N % 2:
        c = 2*H[m+1]
        pc = rising_coeff(p)
        if m+1 < len(pc):
            c -= 2*mp.factorial(N)*mp.zeta(N+1)*pc[m+1]/mp.factorial(p)
        for k in range(1, (m+1)//2+1):
            c -= mp.power(2, 2-2*k)*mp.zeta(2*k)*H[m-2*k+1]
    else:
        for k in range(1, (m+1)//2+1):
            c -= 4*(1-mp.power(2, -2*k))*mp.zeta(2*k)*H[m-2*k+1]
    return (-1)**(m+p)*mp.factorial(m)*c


@lru_cache(None)
def gamma_derivative_at_one(m, k):
    if k == 0:
        return mp.stieltjes(m)
    if m == 0:
        return (-1)**k*mp.factorial(k)*mp.zeta(k+1)
    c = sum(rising_coeff(k)[i]*zjet(k+1, m-i)
            for i in range(min(k, m)+1))
    return (-1)**(m+k)*mp.factorial(m)*c


def gamma_derivative(m, p, x):
    if m == 0:
        return -mp.polygamma(p, x)
    if p == 0:
        return mp.stieltjes(m, x)
    c = sum(rising_coeff(p)[i]*mp.diff(lambda s: mp.zeta(s, x), p+1, m-i)
            /mp.factorial(m-i) for i in range(min(p, m)+1))
    return (-1)**(m+p)*mp.factorial(m)*c


def cot_derivative(r, x):
    return (-1)**r*mp.polygamma(r, 1-x)-mp.polygamma(r, x)


def singular_gamma_polynomial(m, p):
    # d^p(x^-1 log^m x) = x^(-p-1) P(log x).
    c = [0]*m+[1]
    for j in range(p):
        c = [-(j+1)*c[k] + ((k+1)*c[k+1] if k+1 < len(c) else 0)
             for k in range(len(c))]
    return c


def cot_laurent(r, order):
    c = {-r-1: (-1)**r*mp.factorial(r)}
    for j in range(1, (order+r+1)//2+1):
        degree = 2*j-1-r
        if degree < 0:
            continue
        c[degree] = -2*mp.zeta(2*j)*mp.factorial(2*j-1)/mp.factorial(degree)
    return c


def multiply_series(a, b, max_degree):
    out = {}
    for (ea, la), ca in a.items():
        for (eb, lb), cb in b.items():
            if ea+eb <= max_degree:
                key = ea+eb, la+lb
                out[key] = out.get(key, 0)+ca*cb
    return out


def monomial_integral(e, l, b):
    if e == -1:
        return mp.log(b)**(l+1)/(l+1)
    q = e+1
    return b**q*sum((-1)**j*mp.factorial(l)/mp.factorial(l-j)
                    *mp.log(b)**(l-j)/q**(j+1) for j in range(l+1))


def endpoint_integral(m, p, r, order, b, cot_power=None):
    # Smooth gamma Taylor coefficients at one are independent of the
    # coincident cotangent spectral formula being tested.
    g_lower = {(j, 0): gamma_derivative_at_one(m, p+j)/mp.factorial(j)
               for j in range(order+r+p+8)}
    g_upper = {(j, 0): (-1)**j*v for (j, _), v in g_lower.items()}
    for l, v in enumerate(singular_gamma_polynomial(m, p)):
        g_lower[-p-1, l] = mp.mpf(v)
    if cot_power is None:
        ks = {(e, 0): c for e, c in cot_laurent(r, order+p+8).items()}
        sign = (-1)**(r+1)
    else:
        base = {(e, 0): c for e, c in cot_laurent(0, order+p+cot_power+8).items()}
        ks = {(0, 0): mp.mpf(1)}
        for _ in range(cot_power):
            ks = multiply_series(ks, base, order+p+cot_power+4)
        sign = (-1)**cot_power
    lower = multiply_series(g_lower, ks, order)
    upper = multiply_series(g_upper, ks, order)
    return (sum(v*monomial_integral(e, l, b) for (e, l), v in lower.items())
            + sign*sum(v*monomial_integral(e, l, b) for (e, l), v in upper.items()))


def independent_integral(m, p, r, order, b, cot_power=None):
    if cot_power is None:
        f = lambda x: gamma_derivative(m, p, x)*cot_derivative(r, x)
    else:
        f = lambda x: gamma_derivative(m, p, x)*(mp.pi/mp.tan(mp.pi*x))**cot_power
    return endpoint_integral(m,p,r,order,b,cot_power)+mp.quad(f,[b,mp.mpf('.5'),1-b])


def independent_loggamma(r, order, b, cot_power=None):
    lower = {(1,0): -mp.euler, (0,1): -mp.mpf(1)}
    upper = {(1,0): mp.euler}
    for j in range(2,order+r+10):
        lower[j,0] = (-1)**j*mp.zeta(j)/j
        upper[j,0] = mp.zeta(j)/j
    if cot_power is None:
        ks = {(e,0):c for e,c in cot_laurent(r,order+8).items()}
        sign = (-1)**(r+1)
        f = lambda x: mp.loggamma(x)*cot_derivative(r,x)
    else:
        base = {(e,0):c for e,c in cot_laurent(0,order+cot_power+8).items()}
        ks = {(0,0):mp.mpf(1)}
        for _ in range(cot_power):
            ks = multiply_series(ks,base,order+cot_power+4)
        sign = (-1)**cot_power
        f = lambda x: mp.loggamma(x)*(mp.pi/mp.tan(mp.pi*x))**cot_power
    left = multiply_series(lower,ks,order)
    right = multiply_series(upper,ks,order)
    edges = (sum(v*monomial_integral(e,l,b) for (e,l),v in left.items())
             +sign*sum(v*monomial_integral(e,l,b) for (e,l),v in right.items()))
    return edges+mp.quad(f,[b,mp.mpf('.5'),1-b])


def exact_polynomial_checks():
    X, P = sp.symbols('X P')
    D = [X]
    for r in range(15):
        D.append(sp.expand(-(X**2+P)*sp.diff(D[-1], X)))
    C = [sp.Integer(1), sp.Integer(0)]
    c = [{}, {0:sp.Integer(1)}]
    assertions = 0
    for n in range(2, 15):
        C.append(-P*C[n-2])
        cn = {}
        for r in range(n):
            cn[r] = -c[n-1].get(r-1,0)/sp.Integer(n-1)-P*c[n-2].get(r,0)
        c.append(cn)
    for n in range(15):
        rhs = C[n]+sum(a*D[r] for r,a in c[n].items())
        assert sp.expand(rhs-X**n) == 0
        assertions += 1
    return assertions


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dps',type=int,default=50)
    ap.add_argument('--order',type=int,default=80)
    ap.add_argument('--higher-stieltjes',action='store_true')
    ap.add_argument('--exact-only',action='store_true')
    ap.add_argument('--output',default='reflected_collision_checks.json')
    args = ap.parse_args()
    if args.exact_only:
        data = {'status':'PASS','kind':'exact polynomial algebra',
                'exact_polynomial_assertions':exact_polynomial_checks()}
        Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
        print(json.dumps(data))
        return
    mp.mp.dps = args.dps
    b = mp.mpf('0.2')
    cases = [(0,p,r) for p,r in [(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),
                               (0,3),(1,2),(2,1),(3,0),(0,4),(2,2)]]
    if args.higher_stieltjes:
        cases += [(1,0,0),(2,0,0),(1,0,1),(1,1,0),(1,0,2),(1,2,1),(2,3,0)]
    checks = []
    for m,p,r in cases:
        actual = independent_integral(m,p,r,args.order,b)
        expected = prediction(m,p,r)
        err = abs(actual-expected)
        passed = err < mp.power(10,-min(args.dps-10,args.order//2))*(1+abs(expected))
        row = {'m':m,'p':p,'r':r,'actual':str(actual),'predicted':str(expected),
               'absolute_error':str(err),'passed':bool(passed)}
        checks.append(row)
        print(json.dumps(row),flush=True)
    # Direct powers are numerically integrated without converting to K derivatives.
    power_predictions = {
        2: -2*(mp.zeta(2)+mp.diff(mp.zeta,2)),
        3: mp.pi**4/2,
        4: -2*mp.diff(mp.zeta,4)+8*mp.pi**2/3*mp.diff(mp.zeta,2)+mp.mpf(109)/3*mp.zeta(4),
        5: -mp.pi**6/2,
    }
    for q,expected in power_predictions.items():
        actual = independent_integral(0,0,0,args.order,b,cot_power=q)
        err = abs(actual-expected)
        passed = err < mp.power(10,-min(args.dps-10,args.order//2))*(1+abs(expected))
        row = {'m':0,'p':0,'cot_power':q,'actual':str(actual),'predicted':str(expected),
               'absolute_error':str(err),'passed':bool(passed)}
        checks.append(row)
        print(json.dumps(row),flush=True)
    for r in range(4):
        expected = (mp.diff(mp.zeta,0,2)+mp.zeta(2)/2 if r == 0
                    else prediction(0,0,r-1))
        actual = independent_loggamma(r,args.order,b)
        err = abs(actual-expected)
        passed = err < mp.power(10,-min(args.dps-10,args.order//2))*(1+abs(expected))
        row = {'factor':'loggamma','r':r,'actual':str(actual),'predicted':str(expected),
               'absolute_error':str(err),'passed':bool(passed)}
        checks.append(row)
        print(json.dumps(row),flush=True)
    for h in range(1,4):
        odd_harmonic = sum(mp.mpf(1)/(2*j-1) for j in range(1,h+1))
        expected = (-1)**h*mp.pi**(2*h)/2*(mp.log(2*mp.pi)-odd_harmonic)
        actual = independent_loggamma(0,args.order,b,cot_power=2*h)
        err = abs(actual-expected)
        passed = err < mp.power(10,-min(args.dps-10,args.order//2))*(1+abs(expected))
        row = {'factor':'loggamma','cot_power':2*h,'actual':str(actual),'predicted':str(expected),
               'absolute_error':str(err),'passed':bool(passed)}
        checks.append(row)
        print(json.dumps(row),flush=True)
    data = {'working_dps':args.dps,'endpoint_series_degree':args.order,'split':str(b),
            'exact_polynomial_assertions':exact_polynomial_checks(),'checks':checks,
            'all_passed':all(row['passed'] for row in checks),
            'qualification':'Floating-point quadrature and truncated convergent series; not interval-certified.'}
    Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
    assert data['all_passed']


if __name__ == '__main__':
    main()
