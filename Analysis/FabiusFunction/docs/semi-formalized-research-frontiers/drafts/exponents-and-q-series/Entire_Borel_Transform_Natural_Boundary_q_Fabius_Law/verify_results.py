#!/usr/bin/env python3
"""Reproduce finite checks for 'An Entire Borel Transform at a Natural Boundary'.

Exact checks use Fraction arithmetic and two independent coefficient routes.
Numerical checks use mpmath; they are not interval certificates or proofs of
asymptotic assertions. No network access is used.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
import time
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp


def fraction(x: sp.Expr) -> Q:
    p, q = sp.fraction(x)
    return Q(int(p), int(q))


def direct_coefficients(order: int) -> list[dict[int, Q]]:
    """Formal log(sinh(w/2)/(w/2)) and reciprocal of (1-exp(-u))/u."""
    H = [Q(0) for _ in range(order + 2)]
    H[0] = Q(1)
    for j in range(2, order + 2, 2):
        H[j] = Q(1, 2**j * math.factorial(j + 1))
    gamma = [Q(0) for _ in H]
    for j in range(1, len(H)):
        gamma[j] = H[j] - sum(Q(k, j) * gamma[k] * H[j-k]
                              for k in range(1, j))
    E = [Q((-1)**j, math.factorial(j+1)) for j in range(order + 2)]
    D = [Q(1)]
    for j in range(1, len(E)):
        D.append(-sum(E[k] * D[j-k] for k in range(1, j+1)))
    result: list[dict[int, Q]] = [{} for _ in range(order + 1)]
    for j in range(1, order + 1):
        for m in range(1, (j+1)//2 + 1):
            k = j - 2*m + 1
            value = gamma[2*m] * D[k] * Q(2*m)**(k-1)
            if value:
                result[j][2*m] = value
    return result


def bernoulli_coefficients(order: int) -> list[dict[int, Q]]:
    result: list[dict[int, Q]] = [{} for _ in range(order + 1)]
    for j in range(1, order+1):
        for m in range(1, (j+1)//2+1):
            c = fraction(sp.bernoulli(2*m)/(2*m*sp.factorial(2*m)))
            l = j-2*m
            if l == -1:
                value = c/Q(2*m)
            elif l == 0:
                value = c/2
            elif l > 0 and l % 2:
                value = c*fraction(sp.bernoulli(l+1)/sp.factorial(l+1))*(2*m)**l
            else:
                value = Q(0)
            if value:
                result[j][2*m] = value
    return result


@lru_cache(maxsize=None)
def ze(m: int) -> mp.mpf:
    return mp.zeta(2*m)


@lru_cache(maxsize=None)
def odd_coefficient(n: int, z: int = 1) -> mp.mpf:
    a = mp.mpf(abs(z))/2
    S = mp.fsum(ze(m)*ze(n-m)*a**(2*m)*mp.mpf(m)**(2*n-2*m-2)
                for m in range(1, n))
    E = ze(n)*a**(2*n)/(2*mp.mpf(n)**2)
    return (-1)**n * mp.pi**(-2*n)*(S-E)


def log_coefficient_asymptotic(n: int, z: int = 1) -> mp.mpf:
    if n < 2 or z == 0:
        raise ValueError('n must be >= 2 and z must be nonzero')
    N = mp.mpf(n-1)
    w = mp.lambertw(2*mp.e*N/abs(z))
    return (-2*n*mp.log(mp.pi) + mp.log(mp.pi*N/(w*(w+1)))/2
            + 2*N*mp.log(N/w)-2*N+2*N/w)


def borel_imaginary(y: int, z: int = 1, extra_terms: int = 0) -> tuple[mp.mpc, int]:
    """Positive nested sum, with factorial tails kept intact.

    The zeta-minus-one correction is truncated after 120 terms. Its omitted
    portion is bounded relative to cosh(x) by a constant times 4**(-120).
    The outer cutoff is compared at two values by the calling code; that
    comparison is numerical rather than an interval-certified tail bound.
    """
    yy = mp.mpf(y)
    a = mp.mpf(abs(z))/2
    M = a/mp.e*mp.exp(yy/(2*mp.pi))
    cutoff = max(100, int(2*M+100)) + extra_terms
    total = mp.mpf(0)
    for m in range(1, cutoff+1):
        x = m*yy/mp.pi
        term = mp.mpf(1)
        poly = term
        for k in range(1, m):
            term *= x*x/((2*k)*(2*k-1))
            poly += term
        term *= x*x/((2*m)*(2*m-1))
        correction = mp.mpf(0)
        for r in range(120):
            correction += (ze(r+1)-1)*term
            term *= x*x/((2*(m+r)+2)*(2*(m+r)+1))
        total += ze(m)*(a/m)**(2*m)*(mp.cosh(x)-poly+correction)
    alpha = mp.mpf(abs(z))/(2*mp.pi)
    P = mp.fsum(ze(m)*alpha**(2*m)*yy**(2*m-2)
                /(2*m*m*mp.factorial(2*m-2)) for m in range(1, 120))
    Qpart = mp.fsum(ze(m)*alpha**(2*m)*yy**(2*m-1)
                    /(2*m*mp.factorial(2*m-1)) for m in range(1, 120))
    return mp.mpc(-total/mp.pi**2+P, Qpart), cutoff


def borel_power_series(y: int, order: int = 600) -> mp.mpc:
    yy = mp.mpf(y)
    re = mp.fsum((-1)**(n-1)*odd_coefficient(n)*yy**(2*n-2)
                 /mp.factorial(2*n-2) for n in range(1, order+1))
    im = mp.fsum(ze(n)*(1/(2*mp.pi))**(2*n)*yy**(2*n-1)
                 /(2*n*mp.factorial(2*n-1)) for n in range(1, order+1))
    return mp.mpc(re, im)


def F(t: mp.mpc | mp.mpf, z: int = 1, terms: int = 240) -> mp.mpc:
    return mp.fsum((-1)**(m+1)*ze(m)/(mp.mpf(m)*(2*mp.pi)**(2*m))
                   *(z*t)**(2*m)/(-mp.expm1(-2*m*t)) for m in range(1, terms+1))


def cusp(tau: mp.mpf, h: int, z: int = 1, terms: int = 180) -> mp.mpf:
    return -mp.fsum(ze(h*r)*(z*tau/(2*mp.pi))**(2*h*r)
                    /(2*mp.mpf(h*r)**2) for r in range(1, terms+1))


def iterated_cos(s: mp.mpf, m: int, omega: mp.mpf) -> mp.mpf:
    # Avoid cancellation at the origin with the convergent remainder series.
    x = omega*s
    if abs(x) < 1:
        return mp.fsum((-1)**r * omega**(2*r)*s**(2*m+2*r)
                       /mp.factorial(2*m+2*r) for r in range(50))
    polynomial = mp.fsum((-1)**r*x**(2*r)/mp.factorial(2*r) for r in range(m))
    return (-1)**m*(mp.cos(x)-polynomial)/omega**(2*m)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    # ed. (2026-09-30): the default was this directory, so a plain run overwrote the
    # recorded verification_results.json and verification_run.txt; it is now
    # rerun_results/ beside this file. Pass --output-dir . to regenerate the records.
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent/'rerun_results')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 75
    started = time.perf_counter()
    transcript: list[str] = []
    def note(message: str) -> None:
        print(message, flush=True)
        transcript.append(message)
    receipt: dict = {'status': 'running', 'precision_decimal_digits': mp.mp.dps,
        'environment': {'python': platform.python_version(), 'mpmath': mp.__version__,
                        'sympy': sp.__version__},
        'scope': 'Finite exact identities and high-precision numerical checks; not formal or interval certification.'}
    direct = direct_coefficients(60)
    bernoulli = bernoulli_coefficients(60)
    assert direct == bernoulli, 'Independent exact coefficient routes disagree'
    count = sum(len(row) for row in direct)
    note(f'PASS: 60 polynomial coefficient identities ({count} nonzero monomial coefficients).')
    receipt['exact_checks'] = {'polynomial_identities': 60, 'nonzero_monomial_coefficients': count,
        'first_nine_at_z_1': [str(sum(direct[j].values())) for j in range(1,10)]}
    # Compare the zeta formula to independently obtained exact coefficients.
    maxerr = mp.mpf(0)
    for n in range(1, 31):
        for z in (1, 2, 3):
            value = sum(v*Q(z)**k for k, v in direct[2*n-1].items())
            expected = mp.mpf(value.numerator)/value.denominator
            err = abs(odd_coefficient(n,z)-expected)/max(1,abs(expected))
            maxerr = max(maxerr,err)
    assert maxerr < mp.mpf('1e-65')
    note('PASS: 90 zeta/Bernoulli specializations; maximum scaled error '+mp.nstr(maxerr,5))
    receipt['zeta_specializations'] = {'checks':90,'maximum_scaled_error':mp.nstr(maxerr,12)}
    ratios=[]
    for n in (10,25,50,100,250,500,1000):
        ratio=(-1)**n*odd_coefficient(n)/mp.exp(log_coefficient_asymptotic(n))
        row={'n':n,'signed_coefficient_over_leading_asymptotic':mp.nstr(ratio,24)}
        ratios.append(row)
        note(f'Coefficient ratio n={n}: {mp.nstr(ratio,20)}')
    receipt['coefficient_asymptotics']=ratios
    imagrows=[]
    for y in (20,25,30,35,40):
        value,cutoff=borel_imaginary(y)
        check,_=borel_imaginary(y,extra_terms=30)
        stability=abs(value-check)/max(1,abs(value))
        assert stability < mp.mpf('1e-55')
        M=mp.exp(mp.mpf(y)/(2*mp.pi))/(2*mp.e)
        leading=-mp.sqrt(mp.pi*M)*mp.exp(2*M)/(2*mp.pi**2)
        ratio=value/leading
        growth=mp.exp(-mp.mpf(y)/(2*mp.pi))*mp.log(abs(value))
        imagrows.append({'y':y,'M':mp.nstr(M,20),'outer_cutoff':cutoff,
             'ratio_real':mp.nstr(ratio.real,24),'ratio_imag':mp.nstr(ratio.imag,12),
             'scaled_logarithm':mp.nstr(growth,24),'cutoff_comparison':mp.nstr(stability,10)})
        note(f'Borel ratio y={y}: {mp.nstr(ratio,20)}; scaled log={mp.nstr(growth,18)}')
        if y in (20,25,30):
            independent=borel_power_series(y)
            error=abs(value-independent)/max(1,abs(value))
            assert error < mp.mpf('1e-45'), (y,error)
            imagrows[-1]['independent_power_series_error']=mp.nstr(error,12)
    receipt['imaginary_borel_asymptotics']=imagrows
    laplace=[]
    for m in (1,2,3):
        for k in (1,2):
            t=mp.mpf(1)/5
            omega=mp.mpf(m)/(mp.pi*k)
            integral=mp.quad(lambda s:mp.exp(-s/t)*iterated_cos(s,m,omega),[0,1,5,20,mp.inf])
            expected=t**(2*m+1)/(1+(omega*t)**2)
            error=abs(integral-expected)/abs(expected)
            assert error < mp.mpf('1e-55'), (m,k,error)
            laplace.append({'m':m,'k':k,'relative_error':mp.nstr(error,12)})
    receipt['laplace_component_checks']=laplace
    note('PASS: six independent Laplace quadratures of iterated-cosine components.')
    radial=[]
    for name,tau,h in [('pi',mp.pi,1),('2pi/3',2*mp.pi/3,3),('pi/2',mp.pi/2,2)]:
        target=cusp(tau,h)
        for epsstr in ('0.01','0.001','0.0001'):
            eps=mp.mpf(epsstr)
            error=abs(eps*F(eps+1j*tau)-target)
            radial.append({'tau':name,'h':h,'epsilon':epsstr,
                           'target':mp.nstr(target,24),'absolute_error':mp.nstr(error,16)})
    receipt['radial_cusp_checks']=radial
    note('Radial cusp convergence recorded at pi, 2pi/3, and pi/2.')
    receipt['status']='passed'
    receipt['elapsed_seconds']=round(time.perf_counter()-started,3)
    note(f"All finite assertions passed in {receipt['elapsed_seconds']} seconds.")
    # ed. (2026-09-30): newline='\n', so both files are LF on every platform (CRLF on Windows before).
    (args.output_dir/'verification_results.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
    (args.output_dir/'verification_run.txt').write_text('\n'.join(transcript)+'\n',encoding='utf-8',newline='\n')

if __name__ == '__main__':
    main()
