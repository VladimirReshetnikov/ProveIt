#!/usr/bin/env python3
"""Derive density coefficients and the direct-error amplitudes by finite algebra.

The calculation implements equations (A.1)--(A.2) of the article. It is a
symbolic check, not a proof of the uniform analytic remainder estimates.
"""
from pathlib import Path
import argparse
import json
import sympy as s
from verify import rational_c, inverse_coefficients, Q


def derive(order: int) -> dict:
    if not 1 <= order <= 5:
        raise ValueError('This transparent implementation supports orders 1 through 5.')
    z, e, v, sigma = s.symbols('z e v sigma')
    A = 2*s.pi
    n = (order+1)//2
    hs = inverse_coefficients(rational_c(n), Q(0), Q(1))
    hv = [s.Rational(h.numerator, h.denominator) for h in hs]
    Vm = sum((-1)**k*hv[k]*z**(2*k-1) for k in range(1,n+1))
    Vp = 1-sum((2*k-1)*(-1)**k*hv[k]*z**(2*k) for k in range(1,n+1))
    D = s.series(Vp*s.exp(-A*Vm),z,0,order+1).removeO().expand()
    ds = [D.coeff(z,j) for j in range(order+1)]
    moments=[]
    for k in range(2*order+1):
        val=s.expand(e**k*sum(s.binomial(k,l)*(-1/e)**(k-l)
                     *s.rf(1/e+2*sigma,l) for l in range(k+1)))
        moments.append(val)
    expectation=0
    for j in range(order+1):
        g=1/((1+v*v)*v**j)
        val=sum(s.diff(g,v,k).subs(v,1)/s.factorial(k)*moments[k]
                for k in range(2*order+1))
        expectation += ds[j]*A**j*e**j*val
    expectation=s.series(expectation,e,0,order+1).removeO().expand()
    stirling_log=sum((-1)**(r+1)*s.bernoulli(r+1,2*sigma)*e**r/(r*(r+1))
                     for r in range(1,order+1))
    stirling=s.series(s.exp(stirling_log),e,0,order+1).removeO().expand()
    normalized=s.series(2*stirling*expectation,e,0,order+1).removeO().expand()
    Bs=[s.expand(normalized.coeff(e,j)/A**j) for j in range(order+1)]
    assert Bs[0] == 1
    assert s.simplify(Bs[1]-(-s.pi/12+(2*sigma**2-3*sigma+s.Rational(7,12))/(2*s.pi)))==0
    if order >= 2:
        expected=(-sigma**2/12+5*sigma/24-s.Rational(43,288)+s.pi**2/288
                  +(sigma**4/2-11*sigma**3/6+5*sigma**2/3+sigma/48-s.Rational(203,1152))/s.pi**2)
        assert s.simplify(Bs[2]-expected)==0
    for j,B in enumerate(Bs):
        assert s.degree(B,sigma) <= 2*j
    return {'order':order,'density':[str(x) for x in ds],
            'B_minus':[str(x) for x in Bs],
            'B_minus_latex':[s.latex(x) for x in Bs],
            'checked_displayed_coefficients_through':min(order,2),'all_checks_passed':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--order',type=int,default=3)
    args=p.parse_args()
    result=derive(args.order)
    # ed. (2026-09-29): newline='\n' so that a rerun on Windows writes LF, like the filed file.
    Path(__file__).with_name('amplitudes.json').write_text(json.dumps(result,indent=2)+'\n',newline='\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
