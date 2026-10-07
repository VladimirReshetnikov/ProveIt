#!/usr/bin/env python3
"""Bounded floating diagnostics for the exact Gaussian half-axis split.

These quadratures are not interval arithmetic or certified remainder bounds.
The exact Gaussian/parity/composition identities are verified separately in
symbolic_coefficients.py. This program has no output-file or order arguments.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import argparse
from collections import defaultdict
from fractions import Fraction as F
import mpmath as mp
from common import emit, integer, require
from exact_counts import (A, partitions, centralizer, square_roots,
                          involutions, _multiply, _reciprocal)

_COEFFICIENTS=('1','7/24','-119/1152','-7933/414720','1967381/39813120',
               '-57200419/1337720832','6340449533/687970713600')

def _sign(sigma):
    integer(sigma,-1,1,'sector sign')
    require(sigma in (-1,1),'sector sign must be -1 or 1')

def half_axis(n,sigma):
    integer(n,0,12,'half-axis index')
    _sign(sigma)
    with mp.workdps(80):
        norm=mp.exp(-mp.mpf('0.5'))/mp.sqrt(2*mp.pi)
        return norm*mp.quad(lambda x:x**n*mp.exp(-x*x/2+sigma*x),[0,1,mp.inf])

def normalized_half_axis(n,sigma):
    integer(n,100,10000,'normalized index')
    require(n in (100,1000,10000),'normalized index must be 100, 1000, or 10000')
    _sign(sigma)
    with mp.workdps(80):
        N=mp.sqrt(n)
        def integrand(y):
            if y<=-N:
                return mp.mpf(0)
            return mp.exp(n*mp.log1p(y/N)-N*y-y*y/2+sigma*y-mp.mpf('0.25'))/mp.sqrt(mp.pi)
        return mp.quad(integrand,[-N,-10,-3,0,3,10,mp.inf])

def diagnostics():
    with mp.workdps(80):
        N=12
        Jp=[half_axis(n,1) for n in range(N+1)]
        Jm=[half_axis(n,-1) for n in range(N+1)]
        I=[involutions(n) for n in range(N+1)]
        moment_errors=[abs((Jp[n]+(-1)**n*Jm[n])/I[n]-1) for n in range(N+1)]
        require(max(moment_errors)<mp.mpf('1e-70'),'floating moment diagnostic tolerance exceeded')
        product={():F(1)}
        for j in range(1,N+1):
            h={rho:F(1,centralizer(rho)) for rho in partitions(j)}
            product=_multiply(product,_reciprocal(h,N),N)
        rows=[]
        for n in range(N+1):
            weights=defaultdict(F)
            for rho,value in product.items():
                if sum(rho)==n:
                    moved=tuple(k for k in rho if k>=2)
                    weights[sum(moved)]+=value*square_roots(moved)
            exact=sum((value*I[n-s] for s,value in weights.items()),F())
            require(exact==A[n],'exact support weights disagree with the sequence fixture')
            Ap=mp.fsum(mp.mpf(v.numerator)/v.denominator*Jp[n-s] for s,v in weights.items())
            Am=mp.fsum((-1)**s*mp.mpf(v.numerator)/v.denominator*Jm[n-s] for s,v in weights.items())
            residual=abs((Ap+(-1)**n*Am)/A[n]-1)
            require(residual<mp.mpf('1e-70'),'floating sector diagnostic tolerance exceeded')
            rows.append({'n':n,'a_n':A[n],'A_minus':mp.nstr(Am,30),
                         'relative_involution_moment_error':mp.nstr(moment_errors[n],8),
                         'relative_Kostka_decomposition_error':mp.nstr(residual,8)})
        beta=[F(value) for value in _COEFFICIENTS]
        large=[]
        for n in (100,1000,10000):
            for sigma in (-1,1):
                value=normalized_half_axis(n,sigma)
                t=1/mp.sqrt(n)
                truncated=mp.fsum(mp.mpf(c.numerator)/c.denominator*(sigma*t)**j
                                  for j,c in enumerate(beta))
                large.append({'n':n,'sigma':sigma,'normalized_J':mp.nstr(value,35),
                              'residual_div_t7':mp.nstr((value-truncated)/t**7,20)})
        return {'scope':'80-digit floating quadrature diagnostics only; no interval certificate, finite-n asymptotic bound, or certified exponentially accurate remainder.',
                'precision':80,'small_n_max':N,'moment_and_support_diagnostics':rows,
                'large_n_diagnostics':large,
                'exact_algebra':'See the separate symbolic_receipt.json for Gaussian coefficients and parity/composition identities.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    emit(diagnostics())

if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
