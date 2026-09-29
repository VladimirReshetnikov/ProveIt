#!/usr/bin/env python3
"""Reproduce the finite checks in Direct Optimal Truncation of Inverse Harmonic Transseries.

Exact coefficient and sign checks use rational arithmetic. Asymptotic diagnostics
use mpmath; they are not interval certificates or proofs of universal assertions.
Run from any directory. Outputs are written beside this script and in ../figures.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
import platform
import sys
from typing import Sequence
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def rational_c(nmax: int) -> list[Q]:
    ans = [Q(0)]
    for j in range(1, nmax + 1):
        v = -sp.bernoulli(2*j, sp.Rational(1, 2))/(2*j)
        ans.append(Q(int(sp.numer(v)), int(sp.denom(v))))
    return ans


def inverse_coefficients(c: Sequence, zero, one):
    """Finite exponential recurrence; works over Fraction and mpmath.mpf."""
    h = [zero]
    for n in range(1, len(c)):
        a = 2*n - 1
        E = [one]
        for k in range(1, n + 1):
            E.append(one*a/k * sum((j*c[j]*E[k-j] for j in range(1, k+1)), zero))
        h.append(-E[n]/a)
    return h


def mul(a: list[Q], b: list[Q], n: int) -> list[Q]:
    return [sum((a[j]*b[k-j] for j in range(k+1)), Q(0)) for k in range(n+1)]


def formal_residual(c: list[Q], h: list[Q], n: int) -> list[Q]:
    """log(A)+sum c_j z^j A^(-2j), A=1+sum h_j z^j."""
    p = [Q(0)] + h[1:n+1]
    powers = [[Q(1)] + [Q(0)]*n]
    for _ in range(n):
        powers.append(mul(powers[-1], p, n))
    out = [Q(0)]*(n+1)
    for k in range(1, n+1):
        for d in range(n+1):
            out[d] += Q((-1)**(k+1), k)*powers[k][d]
    for j in range(1, n+1):
        for k in range(n-j+1):
            weight = Q(int(sp.binomial(-2*j, k)))
            for d in range(n-j+1):
                out[d+j] += c[j]*weight*powers[k][d]
    return out


def as_mp(q: Q):
    return mp.mpf(q.numerator)/q.denominator


def inverse_value(X):
    root = mp.findroot(lambda w: mp.digamma(w+mp.mpf('.5'))-mp.log(X),
                       X-1/(24*X), solver='newton',
                       df=lambda w: mp.polygamma(1, w+mp.mpf('.5')),
                       tol=mp.mpf(10)**(-mp.mp.dps+15))
    assert abs(mp.digamma(root+mp.mpf('.5'))-mp.log(X)) < mp.mpf(10)**(-mp.mp.dps+20)
    return root


def partial_sum(X, h, n: int):
    return X + mp.fsum(h[j]*X**(1-2*j) for j in range(1, n+1))


def B1(s):
    return -mp.pi/12 + (2*s*s-3*s+mp.mpf(7)/12)/(2*mp.pi)


def B2(s):
    return (-s*s/12+5*s/24-mp.mpf(43)/288+mp.pi**2/288
            +(s**4/2-11*s**3/6+5*s*s/3+s/48-mp.mpf(203)/1152)/mp.pi**2)


def log_interval(r: Q, terms: int = 100) -> tuple[Q, Q]:
    if r <= 0:
        raise ValueError('A positive logarithm argument is required.')
    t = (r-1)/(r+1)
    v = 2*sum((t**(2*k+1)/Q(2*k+1) for k in range(terms)), Q(0))
    e = 2*abs(t)**(2*terms+1)/(Q(2*terms+1)*(1-t*t))
    return v-e, v+e


def sign_certificate(X: int, n: int, h: list[Q], c: list[Q]) -> dict:
    """Exact forward sign at the rational direct partial sum, using a shift.

    psi(v+1/2) = psi(v+L+1/2)-sum_{k=0}^{L-1}1/(v+1/2+k).
    The shifted centered digamma remainder has the sign (-1)^K and is
    strictly smaller than |c_(K+1)|(v+L)^(-2K-2).
    """
    v = Q(X) + sum((h[j]*Q(X)**(1-2*j) for j in range(1, n+1)), Q(0))
    assert v > 0
    shift, K, log_terms = 4, 24, 100
    r = v+shift
    lo, hi = log_interval(r/Q(X), log_terms)
    base = sum((c[j]*r**(-2*j) for j in range(1, K+1)), Q(0))
    base -= sum((1/(v+Q(1,2)+k) for k in range(shift)), Q(0))
    eps = abs(c[K+1])*r**(-2*K-2)
    lower, upper = lo+base, hi+base+eps   # K is even
    expected = (-1)**n
    assert (lower > 0) if expected > 0 else (upper < 0)
    return {'X': X, 'N': n, 'shift': shift, 'forward_order': K,
            'log_terms': log_terms, 'candidate': str(v),
            'residual_lower': str(lower), 'residual_upper': str(upper),
            'expected_sign': expected, 'verified': True,
            'lower_decimal_diagnostic': mp.nstr(as_mp(lower), 18),
            'upper_decimal_diagnostic': mp.nstr(as_mp(upper), 18)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps', type=int, default=190)
    parser.add_argument('--no-figure', action='store_true')
    args = parser.parse_args()
    if args.dps < 160:
        parser.error('Use at least 160 digits to resolve the smallest recorded differences.')
    mp.mp.dps = args.dps
    cq = rational_c(200)
    hq = inverse_coefficients(cq[:21], Q(0), Q(1))
    assert formal_residual(cq, hq, 8) == [Q(0)]*9
    assert hq[1:6] == [Q(-1,24), Q(3,640), Q(-1525,580608),
                        Q(615881,199065600), Q(-3058641,504627200)]
    c = [as_mp(v) for v in cq]
    h = inverse_coefficients(c, mp.mpf(0), mp.mpf(1))
    assert max(abs(h[j]-as_mp(hq[j]))/(1+abs(h[j])) for j in range(1,21)) < mp.mpf('1e-160')
    rows, density, macro, windows = [], [], [], []
    for Xi in [4,8,12,20,30,40]:
        X=mp.mpf(Xi); n=int(mp.floor(mp.pi*X)); sig=n+1-mp.pi*X
        w=inverse_value(X); S=partial_sum(X,h,n); scale=mp.sqrt(X)*mp.exp(-2*mp.pi*X)
        ratio=(-1)**n*(S-w)/scale
        P=lambda v: mp.log(v)+mp.fsum(c[j]*v**(-2*j) for j in range(1,n+1))
        Pd=lambda v: 1/v-mp.fsum(2*j*c[j]*v**(-2*j-1) for j in range(1,n+1))
        u=mp.findroot(lambda v:P(v)-mp.log(X),w,solver='newton',df=Pd,
                      tol=mp.mpf(10)**(-args.dps+15))
        comparison=(-1)**(n+1)*(S-u)/(mp.pi/6*mp.exp(-2*mp.pi*X)/mp.sqrt(X))
        assert ratio > 0
        rows.append({'X':Xi,'N':n,'sigma':mp.nstr(sig,30),
                     'normalized_error':mp.nstr(ratio,40),
                     'through_B2':mp.nstr(1+B1(sig)/X+B2(sig)/X**2,40),
                     'X3_residual':mp.nstr(X**3*(ratio-1-B1(sig)/X-B2(sig)/X**2),25),
                     'comparison_ratio':mp.nstr(comparison,30)})
    ds=[mp.mpf(1),-mp.pi/12,mp.pi**2/288-mp.mpf(1)/24,
        -17*mp.pi/2880-mp.pi**3/10368,
        -mp.mpf(9)/640+11*mp.pi**2/17280+mp.pi**4/497664]
    for ti in [4,8,12,20,30,40]:
        t=mp.mpf(ti); z=mp.j*t
        w=mp.findroot(lambda v:mp.digamma(v+mp.mpf('.5'))-mp.log(z),
                      mp.j*(t+1/(24*t)),solver='newton',
                      df=lambda v:mp.polygamma(1,v+mp.mpf('.5')),
                      tol=mp.mpf(10)**(-args.dps+15))
        rho=-2*mp.re(w)/mp.pi
        ratio=rho/(2*t*mp.exp(-2*mp.pi*t))
        assert rho > 0
        q=mp.exp(2*mp.pi*mp.j*w)
        reflection=-mp.exp(mp.digamma(-w+mp.mpf('.5')))/(z*mp.exp(2*mp.pi*mp.j*q/(1+q)))
        assert abs(reflection-1) < mp.mpf('1e-150')
        density.append({'t':ti,'rho':mp.nstr(rho,40),
                        'normalized_density':mp.nstr(ratio,40),
                        't5_residual':mp.nstr(t**5*(ratio-sum(ds[j]/t**j for j in range(5))),25)})
    for Xi in [12,24,36]:
        X=mp.mpf(Xi); w=inverse_value(X)
        for n in range(int(mp.ceil(mp.pi*X-1-2*mp.sqrt(X))),
                       int(mp.floor(mp.pi*X-1+2*mp.sqrt(X)))+1):
            tau=(n+1-mp.pi*X)/mp.sqrt(X)
            ratio=(-1)**n*(partial_sum(X,h,n)-w)/(mp.sqrt(X)*mp.exp(-2*mp.pi*X))
            assert ratio > 0
            windows.append({'X':Xi,'N':n,'tau':mp.nstr(tau,25),
                            'normalized_error':mp.nstr(ratio,30)})
    for Xi in [20,40]:
        X=mp.mpf(Xi); w=inverse_value(X)
        for target in [mp.mpf('.5'),mp.mpf(1),mp.mpf('1.5')]:
            n=int(mp.floor(target*mp.pi*X))-1
            r=(n+1)/(mp.pi*X)
            ratio=(-1)**n*(partial_sum(X,h,n)-w)/(abs(h[n+1])*X**(-2*n-1))
            macro.append({'X':Xi,'N':n,'r':mp.nstr(r,25),
                          'omitted_term_ratio':mp.nstr(ratio,30),
                          'limiting_profile':mp.nstr(1/(1+r*r),30)})
    certs=[sign_certificate(X,n,hq,cq) for X,n0 in [(2,6),(3,9),(4,12)]
           for n in [n0,n0+1]]
    (ROOT/'verification'/'certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    results={'python':platform.python_version(),'mpmath':mp.__version__,
             'sympy':sp.__version__,'working_digits':args.dps,
             'exact_inverse_coefficients':[str(v) for v in hq[1:]],
             'formal_residual_zero_through':8,'exact_sign_certificates':len(certs),
             'direct':rows,'density':density,'macro_window':macro,'sqrt_window':windows,
             'scope':'Finite exact checks and floating-point diagnostics; not a formal proof.'}
    (ROOT/'verification'/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    lines=['\\begin{tabular}{rrrrr}','\\toprule',
           '$X$ & $N$ & Normalized error & Through $B_2$ & Direct/forward ratio\\\\',
           '\\midrule']
    for r in rows:
        lines.append(f"{r['X']} & {r['N']} & {float(r['normalized_error']):.10f} & "
                     f"{float(r['through_B2']):.10f} & {float(r['comparison_ratio']):.8f}\\\\")
    lines += ['\\bottomrule','\\end{tabular}']
    (ROOT/'verification'/'numeric_table.tex').write_text('\n'.join(lines)+'\n')
    if not args.no_figure:
        import matplotlib.pyplot as plt
        import numpy as np
        fig,ax=plt.subplots(figsize=(7.3,4.5))
        for Xi in [12,24,36]:
            vals=[r for r in windows if r['X']==Xi]
            ax.plot([float(r['tau']) for r in vals],
                    [float(r['normalized_error']) for r in vals],
                    marker='o',markersize=3,linewidth=1,label=f'X = {Xi}')
        ts=np.linspace(-2,2,301)
        ax.plot(ts,np.exp(ts**2/np.pi),linestyle='--',linewidth=1.5,
                label=r'$\exp(\tau^2/\pi)$')
        ax.set_xlabel(r'$\tau=(N+1-\pi X)/\sqrt{X}$')
        ax.set_ylabel(r'$(-1)^N(S_N-W)/(\sqrt{X}\,e^{-2\pi X})$')
        ax.legend();ax.grid(True,alpha=.25);fig.tight_layout()
        fig.savefig(ROOT/'figures'/'truncation_window.pdf')
        fig.savefig(ROOT/'figures'/'truncation_window.png',dpi=190)
        plt.close(fig)
    print(json.dumps({'exact_residual_through':8,'exact_sign_certificates':len(certs),
                      'numerical_cases':len(rows)+len(density)+len(macro)+len(windows),
                      'all_checks_passed':True,'direct':rows},indent=2))


if __name__ == '__main__':
    main()
