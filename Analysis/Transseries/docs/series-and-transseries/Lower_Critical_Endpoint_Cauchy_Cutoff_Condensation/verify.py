#!/usr/bin/env python3
"""Reproducible checks for the lower-critical-endpoint article.

The finite algebra checks are exact. Decimal coefficient, chart, and CDF
checks are diagnostics, not interval certificates or proofs of asymptotics.
Run: python verify.py [--quick]
Dependencies: Python 3.10+, mpmath, sympy, numpy, scipy.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
from fractions import Fraction
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import quad

HERE = Path(__file__).resolve().parent

def mul(a, b, n):
    out = [Fraction(0) for _ in range(n + 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b[:n + 1 - i]):
            out[i + j] += x * y
    return out

def exp_series(a, n):
    assert a[0] == 0
    out = [Fraction(1)] + [Fraction(0)] * n
    for k in range(1, n + 1):
        out[k] = sum(Fraction(j) * a[j] * out[k-j]
                     for j in range(1, k+1)) / k
    return out

def exact_coefficient_checks():
    checks = 0
    for weights in ([Fraction(1,j+1) for j in range(1,13)],
                    [Fraction((j%3)+1, j*j+1) for j in range(1,13)],
                    [Fraction(1) if j in (1,3,6) else Fraction(0)
                     for j in range(1,13)]):
        nmax = 12
        a = [Fraction(0)] + weights
        u = [Fraction(0)] * (nmax+1)
        for _ in range(nmax):
            new = [Fraction(0)] * (nmax+1)
            for j in range(1, nmax+1):
                e = exp_series([j*x for x in u], nmax)
                for k in range(j, nmax+1):
                    new[k] += a[j] * e[k-j]
            u = new
        for n in range(1, nmax+1):
            e = exp_series([n*x for x in a], nmax)
            assert u[n] == e[n]/n
            checks += 1
        # Independent coefficient formula by multiplicity vectors.
        def partitions(total, j=1):
            if total == 0:
                yield []
            elif j <= total:
                for m in range(total//j+1):
                    for rest in partitions(total-m*j, j+1):
                        yield [(j,m)] + rest
        for n in range(1, 9):
            ans = Fraction(0)
            for config in partitions(n):
                term = Fraction(1)
                for j, m in config:
                    term *= (n*a[j])**m / math.factorial(m)
                ans += term
            assert ans/n == u[n]
            checks += 1
    return checks

def exact_chart_checks():
    alpha, R, R1, y, z = sp.symbols('alpha R R1 y z', nonzero=True)
    delta = 2-alpha
    a = -R/alpha
    b = ((5-alpha)*R**2 + 2*y*R*R1)/(2*alpha**2)
    # Expand V^alpha + z V^2 R(yV) - 1, to second order.
    first = sp.simplify(alpha*a + R)
    second = sp.simplify(alpha*b+alpha*(alpha-1)*a*a/2
                         + a*(2*R+y*R1))
    assert first == 0 and second == 0
    return 2

def model(n, epsilon, prefix=None):
    prefix = {} if prefix is None else prefix
    e = mp.mpf(str(epsilon)); alpha = 1+e
    kappa = sum(mp.mpf(j)*mp.mpf(str(p)) for j,p in prefix.items())
    c = 1/(mp.zeta(1+e)+kappa)
    lam = n*c; b = lam**(1/alpha); d = (lam/e)**(1/alpha)
    k = int(mp.floor(b))
    D = n-lam*sum(mp.mpf(j)**(-1-e)+mp.mpf(j)*mp.mpf(str(prefix.get(j,0)))
                 for j in range(1,k+1))
    return e, alpha, c, lam, b, d, D

def probability_coefficient(n, e, c, prefix=None, cutoff=None):
    """Compound Poisson P(K=n), including the original total intensity.

    With cutoff M the result is the joint probability K=n and no action>M,
    so division by the untruncated result gives the exact cutoff ratio.
    Uses long double only as a floating-point diagnostic; checks underflow.
    """
    prefix = {} if prefix is None else prefix
    lam = mp.mpf(n)*c
    m = n if cutoff is None else max(0,min(n,int(cutoff)))
    total = lam*(mp.zeta(2+e)+sum(mp.mpf(str(p)) for p in prefix.values()))
    p0 = np.exp(-np.longdouble(str(total)))
    if not np.isfinite(p0) or p0 <= 0:
        raise ArithmeticError('Floating probability underflow; reduce n or use arbitrary precision.')
    nu = np.zeros(n+1, dtype=np.longdouble)
    ef = np.longdouble(str(e)); lf = np.longdouble(str(lam))
    if m:
        j = np.arange(1,m+1, dtype=np.longdouble)
        nu[1:m+1] = lf*(j**(-2-ef))
        for k, value in prefix.items():
            if k <= m:
                nu[k] += lf*np.longdouble(str(value))
    if np.min(nu) < 0:
        raise ValueError('Negative action intensity.')
    rates = np.arange(n+1, dtype=np.longdouble)*nu
    probs = np.zeros(n+1, dtype=np.longdouble); probs[0] = p0
    for k in range(1,n+1):
        lim = min(k,m)
        if lim:
            probs[k] = np.dot(rates[1:lim+1], probs[k-lim:k][::-1])/k
    if not np.isfinite(probs[n]) or probs[n] <= 0:
        raise ArithmeticError('Nonpositive numerical coefficient.')
    return mp.mpf(str(probs[n]))

def minus_z_cdf(x):
    """Fourier inversion of the explicitly normalized reflected stable law."""
    gamma = float(mp.euler)
    def f(t):
        if t == 0: return 0.0  # an integrable logarithmic endpoint singularity
        return math.exp(-math.pi*t/2)*math.sin(t*(x+1-gamma-math.log(t)))/t
    value, err = quad(f, 0, 35, epsabs=3e-11, epsrel=3e-11, limit=600)
    return 0.5+value/math.pi, err/math.pi

def numeric_checks(quick):
    mp.mp.dps = 70
    rows = []
    ns = [100,500,1500] if quick else [100,500,1500,4000]
    for eps in ['0.1','0.02','0.005']:
        for n in ns:
            e,alpha,c,lam,b,d,D = model(n,eps)
            p = probability_coefficient(n,e,c)
            hahn = (c*mp.gamma(-alpha))**(-1/alpha)*n**(-1/alpha)/(-mp.gamma(-1/alpha))
            rows.append(dict(n=n,epsilon=str(e),lambda_=str(lam),b=str(b),
                             d=str(d),D=str(D),probability=str(p),
                             ratio_uniform=str(p/(e/d)),ratio_dense=str(p/(lam*D**(-1-alpha))),
                             ratio_hahn=str(p/hahn)))
    triangular = []
    for n in ns:
        eps = mp.mpf(n)**(-mp.mpf('0.5'))
        e,alpha,c,lam,b,d,D=model(n,str(eps))
        full=probability_coefficient(n,e,c)
        triangular.append(dict(n=n,epsilon=str(e),lambda_=str(lam),ratio_uniform=str(full/(e/d))))
    prefix_diagnostics=[]
    for prefix in [{1:0.5,2:-0.05},{1:-0.25,3:0.2}]:
        e,alpha,c,lam,b,d,D=model(1500,'0.005',prefix)
        pn=probability_coefficient(1500,e,c,prefix)
        prefix_diagnostics.append(dict(prefix=prefix,ratio_uniform=str(pn/(e/d))))
    sparse = []
    for lam0 in ['0.1','1','5']:
        for n in ns:
            # epsilon=lambda0/n; actual lambda differs by o(1).
            e,alpha,c,lam,b,d,D = model(n,str(mp.mpf(lam0)/n))
            p = probability_coefficient(n,e,c)
            sparse.append(dict(n=n,lambda_target=lam0,lambda_=str(lam),
                               ratio_uniform=str(p/(e/d)),
                               ratio_sparse=str(p/(lam*n**(-1-alpha)))))
    cdfs = [dict(x=x,cdf=minus_z_cdf(x)[0],quadrature_error_estimate=minus_z_cdf(x)[1])
            for x in [-8,-4,-2,0,1,2,3]]
    assert all(0 <= row['cdf'] <= 1 for row in cdfs)
    assert all(cdfs[i]['cdf'] < cdfs[i+1]['cdf'] for i in range(len(cdfs)-1))
    cutoffs=[]
    for n,eps in ([(1500,'0.02')] if quick else [(1500,'0.02'),(4000,'0.02')]):
        e,alpha,c,lam,b,d,D=model(n,eps)
        full=probability_coefficient(n,e,c)
        for x in [-4,-2,0,1]:
            M=int(mp.floor(D+b*x))
            partial=probability_coefficient(n,e,c,cutoff=M)
            cutoffs.append(dict(n=n,epsilon=eps,x=x,M=M,ratio=str(partial/full),limit=minus_z_cdf(x)[0]))
    charts=[]
    for eps in ['0.2','0.05','0.001']:
        e=mp.mpf(eps); alpha=1+e; c=1/mp.zeta(1+e); B=c*mp.gamma(-alpha)
        for x0 in ['0.01','0.001']:
            x=mp.mpf(x0)
            R=lambda w: mp.fsum(mp.zeta(2+e-k)*(-1)**k*w**(k-2)/mp.factorial(k) for k in range(2,32))
            h=x+c*(mp.polylog(2+e,mp.exp(-x))-mp.zeta(2+e))
            phase=B*x**alpha+c*x*x*R(x)
            assert abs(h-phase) < mp.mpf('1e-60')
            y=(h/B)**(1/alpha); z=c/B*y**(1-e)
            V=mp.mpf(1)
            for _ in range(24):
                V=(1+z*V**(1-e)*R(y*V))**(-1/alpha)
            err=abs(y*V-x)
            assert err < mp.mpf('1e-55')
            charts.append(dict(epsilon=eps,x=x0,phase_error=str(abs(h-phase)),chart_error=str(err)))
    shifts=[]
    for eps in ['0.1','0.01','0.001','0.0001']:
        e=mp.mpf(eps); alpha=1+e
        shift=1/e-e**(-1/alpha)
        shifts.append(dict(epsilon=eps,leading_shift_widths=str(shift),log_approximation=str(mp.log(1/e)/alpha)))
    return dict(coefficients=rows,triangular=triangular,prefix_diagnostics=prefix_diagnostics,sparse=sparse,cdf=cdfs,cutoffs=cutoffs,charts=charts,center_shifts=shifts)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    # ed. (2026-09-29): --output (default under build/); writing the recorded
    # verification_results.json needs --overwrite-recorded.
    parser.add_argument('--output', type=Path, default=None,
                        help='default: build/verification_results.json, or build/verification_quick.json with --quick')
    parser.add_argument('--overwrite-recorded', action='store_true',
                        help='allow writing the recorded verification_results.json')
    args=parser.parse_args()
    if args.output is None:
        args.output=HERE/'build'/('verification_quick.json' if args.quick else 'verification_results.json')
    if args.output.resolve()==(HERE/'verification_results.json').resolve() and not args.overwrite_recorded:
        parser.error('refusing to overwrite the recorded verification_results.json; '
                     'pass --overwrite-recorded or choose another --output')
    exact=exact_coefficient_checks()+exact_chart_checks()
    data=dict(status='passed',exact_assertions=exact,
              note='Numerical results are floating-point diagnostics, not interval certificates.',
              long_double_bits=int(np.finfo(np.longdouble).nmant)+1,
              numerical=numeric_checks(args.quick))
    target=args.output
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(f'Passed {exact} exact algebra assertions; numerical diagnostics saved to {target.name}.')
    for row in data['numerical']['coefficients']:
        print('coefficient',row['n'],row['epsilon'],float(mp.mpf(row['ratio_uniform'])),float(mp.mpf(row['ratio_hahn'])))
    for row in data['numerical']['cutoffs']:
        print('cutoff',row)

if __name__=='__main__':
    main()
