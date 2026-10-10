#!/usr/bin/env python3
"""Numerical regressions. Residuals are diagnostics, NOT rigorous error bounds.

Polylogarithm order derivatives, computed by a pole-cancelled Hurwitz DFT,
are compared with the trace formulas.
S4 is tested with integral representations, not the conjecture as evaluator.
Run groups separately: --group traces, --group stieltjes, --group s4.
"""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
from math import gcd
import mpmath as mp
OUT = Path(__file__).resolve().parents[1]/'data'


def record(name, lhs, rhs, start, out):
    residual = abs(lhs-rhs)
    assert residual < mp.mpf(10)**(-mp.mp.dps+8), (name,residual)
    out.append(dict(name=name, working_decimal_digits=mp.mp.dps,
        lhs=str(lhs), rhs=str(rhs), absolute_residual=str(residual),
        elapsed_seconds=round(time.perf_counter()-start,3),
        error_status='floating-point diagnostic, not an interval enclosure'))
    print(name, mp.nstr(residual,5), flush=True)


_jet_cache = {}


def trace(q, derivative, chi=lambda u:1):
    """Evaluate spectral derivatives via the pole-cancelled Hurwitz DFT.

    No Euler product or target trace identity is used in this evaluator.
    Direct mp.diff(polylog) near integral order was numerically unstable in
    the development experiment, so generalized Stieltjes coefficients are
    used instead. The analytic formula is proved in the article.
    """
    dps=mp.mp.dps
    with mp.workdps(dps+12):
        lp=mp.log(q)
        total=0
        us=[u for u in range(1,q) if gcd(u,q)==1]
        for a in range(1,q+1):
            weight=mp.fsum(chi(u)*mp.exp(2j*mp.pi*u*a/q) for u in us)
            value=0
            for j in range(derivative+1):
                key=(q,a,j,mp.mp.dps)
                if key not in _jet_cache:
                    _jet_cache[key]=mp.stieltjes(j,mp.mpf(a)/q)
                value+=mp.binomial(derivative,j)*lp**(derivative-j)*_jet_cache[key]
            total+=weight*value
        total*=(-1)**derivative/mp.mpf(q)
    return +total


def traces(out):
    lp = mp.log
    cases = [
        ('trace30_d0',30,0,lambda u:1,0),
        ('trace30_d1',30,1,lambda u:1,0),
        ('trace30_d2',30,2,lambda u:1,-2*lp(2)*lp(3)*lp(5)),
        ('chi3_level21_d1',21,1,lambda u:1 if u%3==1 else -1,-1j*mp.pi*lp(7)/3),
        ('chi4_level20_d1',20,1,lambda u:1 if u%4==1 else -1,-1j*mp.pi*lp(5)/2),
        ('chi5_level55_d1',55,1,lambda u:1 if u%5 in (1,4) else -1,
         -2*lp((1+mp.sqrt(5))/2)*lp(11))]
    for name,q,j,chi,rhs in cases:
        start=time.perf_counter()
        record(name,trace(q,j,chi),rhs,start,out)
    start=time.perf_counter()
    chi = lambda u: {1:1,2:1j,3:-1j,4:-1}[u%5]
    s=mp.mpf('2.3')+mp.mpf('0.2')*1j
    def direct(q):
        return mp.fsum(chi(u)*mp.polylog(s,mp.exp(2j*mp.pi*u/q))
                       for u in range(1,q) if gcd(u,q)==1)
    record('complex_character_phase_q10',direct(10),
           (2**(1-s)-1j)*direct(5),start,out)


def stieltjes(out):
    coeffs=[lambda s:mp.power(2,s)/(mp.power(2,2*s)-1),
            lambda s:1/(mp.power(2,2*s)-1)]
    points=[mp.mpf(1)/6,mp.mpf(5)/6]
    for n in (0,1,2):
        start=time.perf_counter()
        rhs=mp.mpf(0)
        for C,x in zip(coeffs,points):
            rhs += sum(mp.binomial(n,j)*(-1)**j*mp.diff(C,1,j)*mp.stieltjes(n-j,x)
                       for j in range(n+1))
            rhs -= (-1)**(n+1)*mp.diff(C,1,n+1)/(n+1)
        record(f'underived_stieltjes_n{n}',mp.stieltjes(n,mp.mpf(1)/3),rhs,start,out)
    start=time.perf_counter()
    rhs=mp.mpf(0)
    for C,x in zip(coeffs,points):
        rhs += C(2)*mp.diff(lambda a:mp.stieltjes(1,a),x)
        rhs -= mp.diff(C,2)*mp.diff(lambda a:mp.stieltjes(0,a),x)
    lhs=mp.diff(lambda a:mp.stieltjes(1,a),mp.mpf(1)/3)
    record('derived_stieltjes_k1_n1',lhs,rhs,start,out)


def s4(out):
    start=time.perf_counter()
    def double(a,b):
        f=lambda t:(-mp.log(t))**(a-1)*1j*mp.polylog(b,1j*t)/(1-1j*t)
        return mp.im(mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.75'),1])/mp.factorial(a-1))
    lhs=-mp.quad(lambda x:(-mp.log(x))**3*mp.log1p(x*x)/(1+x*x),
                 [0,mp.mpf('.25'),mp.mpf('.75'),1])/6
    beta4=mp.im(mp.polylog(4,1j))
    rhs=(4*double(4,1)-3*double(3,2)-9*double(2,3))/7+mp.pi**5/224 \
        -27*mp.catalan*mp.zeta(3)/224-2*beta4*mp.log(2)
    record('S4_conjecture_integral_comparison',lhs,rhs,start,out)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--group',choices=['traces','stieltjes','s4'],required=True)
    ap.add_argument('--dps',type=int,default=55)
    args=ap.parse_args()
    if args.dps < 25:
        raise ValueError('At least 25 digits are required.')
    mp.mp.dps=args.dps
    out=[]
    globals()[args.group](out)
    OUT.mkdir(exist_ok=True)
    (OUT/f'numeric_{args.group}.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':
    main()
