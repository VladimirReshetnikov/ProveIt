#!/usr/bin/env python3
"""Interval certificate for the Rvachev shell-RMS correction.

Run: python certify_constants.py --output constants_certificate.json
Requires mpmath. All final comparisons use exact Fraction endpoints of the
interval calculations. No ordinary floating-point result is used to certify
an inequality. The proof of the truncation/aliasing bounds is in article.tex.
This is a reproducible interval computation, not a proof-assistant certificate.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
import platform
import time
import mpmath
from mpmath import iv

R = 4
K = 128
N = 512
J = 28
C = 3_200_000
DPS = 35

@lru_cache(maxsize=None)
def alpha(k: int) -> int:
    if k < 0:
        raise ValueError('alpha is indexed by nonnegative integers')
    if k == 0:
        return 0
    if k == 1:
        return 1
    if k % 2 == 0:
        return -2 * alpha(k // 2)
    return alpha(k // 2) + alpha(k // 2 + 1)

@lru_cache(maxsize=None)
def eta(k: int) -> Fraction:
    if k < 0:
        raise ValueError('eta is indexed by nonnegative integers')
    if k == 0:
        return Fraction(1)
    if k == 1:
        return Fraction(-1, 3)
    if k % 2 == 0:
        return eta(k // 2)
    return -(eta(k // 2) + eta(k // 2 + 1)) / 2

def as_iv(q: Fraction | int):
    q = Fraction(q)
    return iv.mpf(q.numerator) / q.denominator

def endpoint_fraction(t: tuple[int, int, int, int]) -> Fraction:
    """Convert a finite mpmath mpf tuple to its exact rational value."""
    sign, mantissa, exponent, _ = t
    if not isinstance(exponent, int):
        raise ArithmeticError('Nonfinite interval endpoint')
    q = Fraction(-mantissa if sign else mantissa)
    return q * (2 ** exponent) if exponent >= 0 else q / (2 ** (-exponent))

def endpoints(x) -> tuple[Fraction, Fraction]:
    # _mpi_ is the exact internal pair of arbitrary-precision binary endpoints.
    return tuple(endpoint_fraction(t) for t in x._mpi_)

def outward_decimal(q: Fraction, lower: bool) -> str:
    with localcontext() as ctx:
        ctx.prec = 22
        ctx.rounding = ROUND_FLOOR if lower else ROUND_CEILING
        return str(Decimal(q.numerator) / Decimal(q.denominator))

def record(lo: Fraction, hi: Fraction) -> dict:
    if lo > hi:
        raise ArithmeticError('Reversed enclosure')
    return {
        'lower_rational': str(lo), 'upper_rational': str(hi),
        'lower_decimal_outward': outward_decimal(lo, True),
        'upper_decimal_outward': outward_decimal(hi, False),
    }

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('constants_certificate.json'))
    args = parser.parse_args()
    iv.dps = DPS
    start = time.monotonic()
    M = N * 2 ** R
    assert 2 * K < N and J >= 2
    tail = Fraction(20, 9 * 4 ** J)
    tail_interval = iv.mpf([as_iv(1-tail).a, 1])
    log2 = iv.ln(2)
    kappa = iv.ln(2 * iv.pi) / log2
    H = []
    sin2 = []
    print(f'Computing {M} interval samples (dps={DPS}, J={J})...', flush=True)
    for q in range(M):
        x = iv.mpf(q) / M
        z = (1+x)/2
        product = iv.mpf(1)
        t = iv.pi * z
        for _ in range(J):
            product *= iv.sin(t) / t
            t /= 2
        phi = product * tail_interval
        L = iv.ln(1+x)
        H.append((phi/iv.pi)**2 * iv.exp(L*L/log2 + (2*kappa-2)*L))
        sin2.append(iv.sin(iv.pi*x)**2)
    g = []
    for j in range(N):
        value = iv.mpf(0)
        for ell in range(2**R):
            q = j + ell*N
            weight = iv.mpf(1)
            for p in range(R):
                weight *= sin2[(2**p*q) % M]
            value += weight * H[q]
        g.append(value)
    cosine = [iv.cos(2*iv.pi*j/N) for j in range(N)]
    est_a, est_mu = iv.mpf(0), iv.mpf(0)
    for j in range(N):
        kernel_a, kernel_mu = iv.mpf(0), iv.mpf(1)
        for k in range(1, K+1):
            co = cosine[(j*k) % N]
            kernel_a += 2*alpha(k)*co
            kernel_mu += 2*as_iv(eta(k))*co
        est_a += g[j] * kernel_a
        est_mu += g[j] * kernel_mu
    est_a *= Fraction((-2)**R, N).numerator
    est_a /= Fraction((-2)**R, N).denominator
    est_mu /= N
    err_a = Fraction(16*C, 3*K**6) + Fraction(64*C*K*(K+1), (N-K)**8)
    err_mu = Fraction(2*C, 7*K**7) + Fraction(4*C*(2*K+1), (N-K)**8)
    alo, ahi = endpoints(est_a)
    mlo, mhi = endpoints(est_mu)
    alo, ahi = alo-err_a, ahi+err_a
    mlo, mhi = mlo-err_mu, mhi+err_mu
    root_iv = iv.sqrt(iv.mpf([as_iv(mlo).a, as_iv(mhi).b])/2)
    rlo, rhi = endpoints(root_iv)
    targets = {
        'alpha_H': ('-0.002907', '-0.002898'),
        'mu_H': ('0.021221672', '0.021221677'),
        'RMS_limit': ('0.10300890', '0.10300894'),
    }
    enclosures = {'alpha_H': (alo,ahi), 'mu_H': (mlo,mhi), 'RMS_limit': (rlo,rhi)}
    for name, (lo,hi) in enclosures.items():
        lower, upper = map(Fraction, targets[name])
        assert lower < lo <= hi < upper, f'Target enclosure failed: {name}'
        print(name, record(lo,hi), flush=True)
    assert ahi < 0 < mlo
    result = {
        'status': 'PASS',
        'arithmetic': 'mpmath.iv outward interval arithmetic; exact Fraction final comparisons',
        'proof_assistant_checked': False,
        'python': platform.python_version(), 'mpmath': mpmath.__version__,
        'parameters': {'r':R,'K':K,'N':N,'J':J,'C':C,'interval_dps':DPS},
        'sinc_tail_error': str(tail),
        'analytic_errors': {'alpha_H':str(err_a),'mu_H':str(err_mu)},
        'enclosures': {name:record(*bounds) for name,bounds in enclosures.items()},
        'certified_coarse_open_intervals':targets,
        'elapsed_seconds_diagnostic_only':round(time.monotonic()-start,2),
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(f'PASS: wrote {args.output}', flush=True)

if __name__ == '__main__':
    main()
