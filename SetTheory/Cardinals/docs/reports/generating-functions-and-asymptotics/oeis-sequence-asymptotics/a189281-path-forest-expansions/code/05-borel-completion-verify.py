#!/usr/bin/env python3
"""Reproduce exact checks and optional high-precision numerical diagnostics.

Run from any directory: python code/verify.py --numerical
All paths are anchored at the script. Exact assertions do not depend on OEIS
recurrences. Numerical assertions are consistency checks, not rigorous error bounds.
"""
from __future__ import annotations
import argparse
import csv
import json
import sys
from fractions import Fraction
from itertools import permutations
from math import factorial
from pathlib import Path
from core import (correction_coefficients, exact_a, numerical_H,
                  numerical_canonical, recurrence_rhs)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'

OEIS_VALUES = [1,1,2,5,18,75,410,2729,20906,181499,1763490,18943701,
              222822578,2847624899,39282739034,581701775369,9202313110506,
              154873904848803,2762800622799362,52071171437696453,
              1033855049655584786,21567640717569135515]
OEIS_C = [1,3,2,1,0,3,26,101,124,-1409,-13266]


def formal_psi(order):
    """Independently expand (1+z)^3 sum j![-z^2/(1+z)]^j."""
    from math import comb
    out = [0]*(order+1)
    for j in range(order//2+1):
        a = 3-j
        for k in range(order-2*j+1):
            if a >= 0:
                v = comb(a,k) if k <= a else 0
            else:
                v = (-1)**k*comb(-a+k-1,k)
            out[2*j+k] += (-1)**j*factorial(j)*v
    return out


def check_volterra_coefficients(order, psi):
    """Verify the Dawson/Green-function formula entirely in exact rationals.

    g_v satisfies g''+g'+v*g=0, g(0)=0,g'(0)=1. Integrating each
    v-polynomial against exp(-v) replaces v^k by k!.
    """
    # Derivative values of g, as polynomials in v (ascending coefficients).
    g = [[0], [1]]
    for m in range(order+2):
        a, b = g[-1], [0]+g[-2]
        g.append([-((a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0))
                  for j in range(max(len(a),len(b)))])
    k = [sum(a*factorial(j) for j,a in enumerate(p)) for p in g]
    for m in range(order):
        h = k[m+2]+4*k[m+1]+6*k[m]
        if m >= 1: h += 4*k[m-1]
        if m >= 2: h += k[m-2]
        assert h == psi[m+1], (m,h,psi[m+1])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=400)
    parser.add_argument('--numerical',action='store_true')
    parser.add_argument('--dps',type=int,default=70)
    args=parser.parse_args()
    if args.order < 40: parser.error('--order must be at least 40')
    if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
    DATA.mkdir(exist_ok=True)
    report=[]
    def log(s): print(s,flush=True);report.append(s)
    psi,c=correction_coefficients(args.order)
    assert psi==formal_psi(args.order)
    log(f'PASS exact: {args.order+1} auxiliary coefficients from two independent constructions.')
    assert c[:len(OEIS_C)]==OEIS_C
    log('PASS exact: 11 displayed OEIS asymptotic coefficients reproduced without a guessed recurrence.')
    check_volterra_coefficients(args.order-1,psi)
    log(f'PASS exact: {args.order-1} Taylor derivatives in the Gaussian--Volterra representation.')
    # Polynomial differential equation for H.
    for m in range(args.order-4):
        lhs=2*psi[m+4]+3*psi[m+3]+(m+5)*psi[m+2]+(m-1)*psi[m+1]
        rhs=6 if m==0 else (1 if m==1 else 0)
        assert lhs==rhs,(m,lhs,rhs)
    log(f'PASS exact: {args.order-4} coefficient identities in the third-order H equation.')
    values=[exact_a(n) for n in range(31)]
    assert values[:len(OEIS_VALUES)]==OEIS_VALUES
    log('PASS exact: 22 OEIS values agree with independent path-tiling enumeration; generated n=0..30.')
    checked=0
    for n in range(9):
        count=0
        for p in permutations(range(n)):
            checked+=1
            count+=all(p[i+2]-p[i]!=2 for i in range(n-2))
        assert count==values[n]
    log(f'PASS exact: exhaustive enumeration of {checked:,} permutations, sizes 0..8.')
    (DATA/'coefficients.json').write_text(json.dumps({'order':args.order,'psi':psi,'c':c},indent=2)+'\n')
    (DATA/'exact_values.json').write_text(json.dumps({'a':values},indent=2)+'\n')
    if args.numerical:
        import mpmath as mp
        mp.mp.dps=args.dps
        ns=[4,8,12,16,20,24,30]
        cache={}
        rows=[]
        for n in ns:
            b=numerical_canonical(n);cache[n]=b
            v=mp.e*mp.mpf(values[n])/mp.factorial(n)
            m=min(len(c)-1,max(1,int(n*(mp.log(n)/2-1))))
            partial=mp.fsum(mp.mpf(c[j])/mp.mpf(n)**j for j in range(m+1))
            rows.append({'n':n,'C_star':mp.nstr(b,45),
                         'normalized_exact':mp.nstr(v,45),
                         'exact_minus_C_star':mp.nstr(v-b,24),
                         'M':m,'C_star_minus_partial':mp.nstr(b-partial,24)})
            log(f'DIAGNOSTIC n={n}: exact-minus-canonical = {mp.nstr(v-b,14)}; M={m}.')
        # Four values used to verify the shift equation, including nonintegral arguments.
        for n in [mp.mpf('7.5'),mp.mpf(10)]:
            ss=[numerical_canonical(n-k) for k in range(4)]
            lhs=(2*n*(n-1)*(n-2)*ss[0]+2*(n-1)*(n-2)*ss[1]
                 +(n-2)*(n+1)*ss[2]+(n-4)*ss[3])
            rel=abs(lhs-recurrence_rhs(n))/(1+abs(lhs))
            assert rel < mp.mpf(10)**(-args.dps+15),mp.nstr(rel,20)
            log(f'DIAGNOSTIC shift equation at n={n}: relative residual {mp.nstr(rel,4)}.')
        for y in [8,12,20]:
            h=numerical_H(mp.j*y)
            lead=-mp.j*mp.sqrt(mp.pi)*mp.exp(-mp.mpf(1)/4)*y*y/4*mp.exp(y*y/4-mp.j*y/2)
            log(f'DIAGNOSTIC imaginary-axis ratio y={y}: {mp.nstr(h/lead,12)}.')
        with (DATA/'numerical_diagnostics.csv').open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
        (DATA/'numerical_status.json').write_text(json.dumps({'precision_digits':args.dps,
            'interval_certified':False,'method':'mpmath quadrature; diagnostics only'},indent=2)+'\n')
    (DATA/'verification.txt').write_text('\n'.join(report)+'\n')

if __name__=='__main__': main()
