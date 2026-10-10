#!/usr/bin/env python3
"""Independent numerical checks of the translation identities.

Run with Python 3 and mpmath. These are numerical diagnostics, not
interval certificates or substitutes for the analytic proofs.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def variance_integral(h):
    h = mp.mpf(h)
    f = mp.loggamma
    return (mp.quad(lambda x: (f(x+h)-f(x))**2, [0, (1-h)/2, 1-h])
            + mp.quad(lambda y: (f(y)-f(1-h+y))**2, [0, h/2, h]))


def variance_hurwitz(h):
    z1 = lambda a: mp.zeta(-1, a, derivative=1)
    z2 = lambda a: mp.zeta(-1, a, derivative=2)
    return (z2(h)+z2(1-h)-2*z2(1)
            + 2*(z1(h)+z1(1-h)-2*z1(1))
            + (2+mp.pi**2/3)*h*(1-h))


def variance_polylog(h, p, q):
    # Evaluate order derivatives by the finite Hurwitz Fourier transform.
    # Numerical finite differences of polylog at integer order can lose
    # precision through removable singularities in its implementation.
    z = mp.exp(2j*mp.pi*p/q)
    c = mp.euler + mp.log(2*mp.pi)
    def order_derivative(r):
        return mp.power(q,-2)*mp.fsum(z**k*mp.fsum(
            mp.binomial(r,j)*(-mp.log(q))**(r-j)
            *mp.zeta(2,mp.mpf(k)/q,derivative=j)
            for j in range(r+1)) for k in range(1,q+1))
    gaps = [mp.zeta(2, derivative=r)
            - mp.re(order_derivative(r))
            for r in range(3)]
    return ((c*c+mp.pi**2/4)*gaps[0]-2*c*gaps[1]+gaps[2])/mp.pi**2


def coefficients(count):
    return [(j, mp.harmonic(2*j-2)*mp.zeta(2*j-1)
             + mp.zeta(2*j-1, derivative=1)) for j in range(2, count+1)]


def variance_series(h, coeff):
    ell = mp.log(1/h)
    return (h*(ell*ell+2*ell+2+mp.pi**2/3)
            + (2*mp.stieltjes(1)-mp.pi**2/3)*h*h
            - mp.fsum(2*b*h**(2*j)/(j*(2*j-1)) for j,b in coeff))


def variance_tail_bound(h, count):
    j = count+1
    return 2*mp.zeta(3)*(1+mp.log(2*j))*h**(2*j)/(j*j*(1-h*h))


def accelerated_stieltjes(count):
    q = mp.fsum((mp.harmonic(2*j-2)*(mp.zeta(2*j-1)-1)
                 + mp.zeta(2*j-1, derivative=1))/(j*(2*j-1))
                for j in range(2,count+1))
    return 2*mp.log(2)-mp.log(2)**2-1+q


def accelerated_tail_bound(count):
    j = count+1
    return mp.mpf(16)/3*(2+mp.log(2*j))*mp.power(4,-j)/(j*j)


def germ_formula(s,t,h):
    u = s+t
    r = (mp.gamma(1-s)*mp.gamma(1-t)/mp.gamma(2-u)
         *mp.cos(mp.pi*(s-t)/2)/mp.cos(mp.pi*u/2))
    return r*(mp.zeta(u-1,h)+mp.zeta(u-1,1-h)-2*mp.zeta(u-1))


def germ_integral(s,t,h):
    def first(x):
        return ((mp.zeta(s,x+h)-mp.zeta(s,x))
                *(mp.zeta(t,x+h)-mp.zeta(t,x)))
    def second(y):
        return ((mp.zeta(s,y)-mp.zeta(s,1-h+y))
                *(mp.zeta(t,y)-mp.zeta(t,1-h+y)))
    return mp.quad(first,[0,(1-h)/2,1-h])+mp.quad(second,[0,h/2,h])


def run(dps):
    mp.mp.dps = dps
    records=[]
    def record(label, lhs, rhs, tolerance=None):
        error=abs(lhs-rhs)
        tolerance = tolerance if tolerance is not None else mp.power(10,-dps+12)
        records.append(dict(label=label, lhs=mp.nstr(lhs,dps),
                            rhs=mp.nstr(rhs,dps), error=mp.nstr(error,12),
                            tolerance=mp.nstr(tolerance,12), passed=bool(error<tolerance)))
        print(label, 'PASS' if error<tolerance else 'FAIL', mp.nstr(error,6), flush=True)
    coeff=coefficients(100)
    for raw in ['0.125','0.3','0.5','0.8','0.0001']:
        h=mp.mpf(raw)
        v=variance_integral(h)
        record('gamma integral vs Hurwitz, h='+raw,v,variance_hurwitz(h))
        if raw in ['0.3','0.5']:
            p,q = (3,10) if raw=='0.3' else (1,2)
            record('gamma integral vs polylog Fourier jets, h='+raw,v,variance_polylog(h,p,q))
        record('gamma integral vs odd-zeta series, h='+raw,v,variance_series(h,coeff),
               variance_tail_bound(h,100)+mp.power(10,-dps+12))
    for s,t,h in [(mp.mpf('-.17'),mp.mpf('-.23'),mp.mpf('.3')),
                  (mp.mpc('-.11','.07'),mp.mpc('-.19','-.05'),mp.mpf('.4'))]:
        record('two-order analytic germ '+str((s,t,h)),germ_integral(s,t,h),germ_formula(s,t,h))
    for count in [12,24,48,80]:
        record('accelerated gamma1, J='+str(count),accelerated_stieltjes(count),mp.stieltjes(1),
               accelerated_tail_bound(count)+mp.power(10,-dps+8))
    h=mp.mpf('.37')
    second=mp.diff(variance_hurwitz,h,2)
    expected=2*(mp.stieltjes(1,h)+mp.stieltjes(1,1-h)-mp.pi**2/3)
    record('second derivative and Stieltjes reflection',second,expected)
    maximum=variance_hurwitz(mp.mpf('.5'))
    return dict(dps=dps,proof_status='numerical diagnostic only',
                maximum_variance=mp.nstr(maximum,dps),records=records,
                all_passed=all(x['passed'] for x in records))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=55)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'verification'/'translation_results.json')
    args=parser.parse_args()
    result=run(args.dps)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if not result['all_passed']:
        raise SystemExit(1)
