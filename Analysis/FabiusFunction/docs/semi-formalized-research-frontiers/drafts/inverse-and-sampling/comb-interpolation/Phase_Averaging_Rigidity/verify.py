#!/usr/bin/env python3
"""Reproducible checks for Rvachev quadrature phase rigidity.

Exact tests use only fractions.Fraction and the standard library. Optional
mpmath tests are numerical diagnostics, not interval certificates or proofs.
No network access is used. See the article for proofs of the evaluator.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, gcd
import json
from pathlib import Path
from typing import Any

@lru_cache(None)
def moment(r: int) -> F:
    if r < 0:
        raise ValueError("Moment order must be nonnegative")
    if r == 0:
        return F(1)
    if r % 2:
        return F(0)
    return sum((F(comb(r, j), j + 1) * moment(r-j)
                for j in range(2, r+1, 2)), F(0)) / (2**r - 1)

@lru_cache(None)
def up(x: F) -> F:
    """Exact up(x) for a dyadic rational, using a finite convolution cell."""
    x = abs(F(x))
    if x >= 1:
        return F(0)
    den = x.denominator
    if den & (den - 1):
        raise ValueError("The exact evaluator requires a dyadic rational")
    N = den.bit_length()  # denominator=2^d => N=d+1
    if x == 0:
        return F(1)
    total = F(0)
    for m in range(2**N):
        a = x + 1 - F(1, 2**N) - F(m, 2**(N-1))
        if a <= 0:
            break
        term = sum((F(comb(N-1, j)) * a**(N-1-j) *
                    F(1, 2**(N*j)) * moment(j)
                    for j in range(0, N, 2)), F(0))
        total += (-1 if m.bit_count() % 2 else 1) * term
    return F(2**(N*(N-1)//2), factorial(N-1)) * total

@lru_cache(None)
def quadrature(M: int, theta: F, r: int) -> F:
    if M < 1 or M & (M-1):
        raise ValueError("Exact single-phase tests use a power-of-two mesh")
    theta = F(theta) % 1
    return sum((F(k+theta, M)**r * up(F(k+theta, M))
                for k in range(-M, M+1)), F(0)) / M

def valuation2(n: int) -> int:
    n = abs(n)
    if not n:
        raise ValueError("v2(0) is not used")
    return (n & -n).bit_length() - 1

def exact_checks(max_level: int) -> dict[str, Any]:
    checks = 0
    samples = []
    assert moment(2) == F(1,9)
    assert moment(4) == F(19,675)
    checks += 2
    assert up(F(1,2)) == F(1,2)
    assert up(F(1,4)) == F(67,72)
    assert up(F(3,4)) == F(5,72)
    checks += 3
    for d in range(max_level+1):
        M, p = 2**d, d+1
        selected = {F(0), F(1,2)} if d % 2 == 0 else {F(1,4), F(3,4)}
        for h in range(8):
            theta = F(h,8)
            for r in range(d+1):
                assert quadrature(M,theta,r) == moment(r), (M,theta,r)
                checks += 1
            defect = quadrature(M,theta,p)-moment(p)
            assert (defect == 0) == (theta in selected), (M,theta,p,defect)
            checks += 1
        samples.append({"mesh":M,"threshold_degree":p,
                        "defect_at_zero":str(quadrature(M,F(0),p)-moment(p)),
                        "defect_at_quarter":str(quadrature(M,F(1,4),p)-moment(p))})
    # Compare explicit cyclic phase averaging with the reindexed fine mesh.
    for d in range(min(max_level,3)+1):
        M=2**d
        for s in (1,2):
            L=2**s
            for theta in (F(0), F(1,8), F(3,8)):
                for r in range(d+s+1):
                    averaged=sum((quadrature(M,theta+F(j,L),r)
                                  for j in range(L)),F(0))/L
                    assert averaged == quadrature(L*M,L*theta,r) == moment(r)
                    checks += 1
    # Exact arithmetic characterization of the permitted Fourier indices.
    arithmetic_checks=0
    for a in range(1,17):
        for b in range(1,13):
            if gcd(a,b)!=1:
                continue
            for r in range(7):
                L=b*2**max(0,r-valuation2(a))
                for n in range(1,65):
                    t=F(a*n,b)
                    good=t.denominator==1 and valuation2(t.numerator)>=r
                    assert good == (n%L==0)
                    arithmetic_checks += 1
    return {"exact_quadrature_assertions":checks,
            "exact_frequency_arithmetic_assertions":arithmetic_checks,
            "max_dyadic_level":max_level,"threshold_defect_table":samples,
            "moment_values":{str(j):str(moment(j)) for j in range(0,11,2)}}

def numerical_checks() -> dict[str, Any]:
    try:
        import mpmath as mp
    except ImportError:
        return {"status":"skipped: mpmath is not installed"}
    mp.mp.dps=75
    @lru_cache(None)
    def H(t):
        t=mp.mpf(t)
        result=mp.mpf(1)
        for k in range(270):
            z=mp.pi*t/(mp.mpf(2)**k)
            if z:
                result *= mp.sin(z)/z
        return result
    dilation_checks=0
    largest_scaled_ratio=mp.mpf(0)
    for q in range(1,32,2):
        base=H(mp.mpf(q)/2)
        assert mp.sign(base)==(-1)**(q.bit_count()-1)
        for n in range(3,32,2):
            ratio=abs(H(mp.mpf(q*n)/2)/base)
            assert ratio <= mp.mpf(1)/(n*n) * (1+mp.mpf('1e-65'))
            m=n.bit_length()-1
            envelope=mp.mpf(2)**(m*(m+1)//2-1)/mp.mpf(n)**(m+1)
            smooth=mp.exp(-mp.log(n)**2/(2*mp.log(2)))/(2*mp.sqrt(n))
            assert ratio <= envelope * (1+mp.mpf('1e-65'))
            assert envelope <= smooth * (1+mp.mpf('1e-65'))
            largest_scaled_ratio=max(largest_scaled_ratio,n*n*ratio)
            dilation_checks += 1
    # Direct differentiation of the product versus the leading-zero formula.
    derivative_checks=0
    for d in range(4):
        p=d+1
        for q in (1,3,5):
            M=(2**d)*q
            for n in (1,3,5):
                value=mp.diff(H,mp.mpf(M*n),p)
                predicted=-mp.factorial(p)*H(mp.mpf(q*n)/2)/(mp.mpf(M*n)**p)
                assert abs(value-predicted) <= abs(predicted)*mp.mpf('1e-50')
                derivative_checks += 1
    # Cross-check signs and all normalization factors against exact dyadic sums.
    # Only the first 200 odd harmonics are needed at the chosen tolerances.
    fourier_checks=0
    max_error=mp.mpf(0)
    for d in range(4):
        M,p=2**d,d+1
        eps=(-1)**((p-1)//2)
        A=2*mp.factorial(p)*eps*H(mp.mpf('0.5'))/(2*mp.pi*M)**p
        for theta in (F(1,8), F(1,4), F(3,8)):
            tt=mp.mpf(theta.numerator)/theta.denominator
            trig=mp.sin if p%2 else mp.cos
            series=sum((H(mp.mpf(n)/2)/H(mp.mpf('0.5'))/n**p*
                        trig(2*mp.pi*n*tt) for n in range(1,400,2)),mp.mpf(0))
            exact=quadrature(M,theta,p)-moment(p)
            ex=mp.mpf(exact.numerator)/exact.denominator
            err=abs(A*series-ex)
            assert err < mp.mpf('1e-18'), (M,str(theta),err)
            max_error=max(max_error,err)
            fourier_checks += 1
    return {"status":"passed; floating-point diagnostics, not certified intervals",
            "decimal_precision":75,"odd_dilation_checks":dilation_checks,
            "multiscale_envelope_checks":dilation_checks,
            "leading_derivative_checks":derivative_checks,
            "Fourier_normalization_checks":fourier_checks,
            "largest_n_squared_ratio_sample":mp.nstr(largest_scaled_ratio,25),
            "maximum_Fourier_error_sample":mp.nstr(max_error,10),
            "eta_values":{str(p):mp.nstr((1-mp.mpf(2)**(-p-1))*mp.zeta(p+1)-1,25)
                          for p in range(1,7)}}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-level', type=int, default=4)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    parser.add_argument('--skip-numerical', action='store_true')
    args=parser.parse_args()
    if not 0<=args.max_level<=7:
        parser.error('--max-level must lie between 0 and 7')
    result={"repository_snapshot":"37e61c1fdec28c6e7ab7ff445043993077b42cbd",
            "exact":exact_checks(args.max_level)}
    if not args.skip_numerical:
        result['numerical']=numerical_checks()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
