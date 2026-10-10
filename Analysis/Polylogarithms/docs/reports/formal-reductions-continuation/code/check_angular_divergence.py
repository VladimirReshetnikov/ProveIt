#!/usr/bin/env python3
"""Exact coefficient checks for the angular divergence theorem.

The theorem is proved symbolically for all s in the article. These finite
checks compile the displayed polynomials using rational power series and
cross-check small cases against direct symbolic trigonometric expansion.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import sympy as sp

def mul(a,b,d):
    out=[F(0)]*(d+1)
    for j,x in enumerate(a):
        for k,y in enumerate(b[:d+1-j]):out[j+k]+=x*y
    return out

def power(p,k,d):
    out=[F(1)]+[F(0)]*d
    for _ in range(k):out=mul(out,p,d)
    return out

def inverse(p,d):
    out=[1/p[0]]
    for j in range(1,d+1):
        out.append(-sum(p[k]*out[j-k] for k in range(1,j+1))/p[0])
    return out

def even_cos(t,d):
    return [F((-1)**(j//2)*t**j,factorial(j)) if j%2==0 else F(0) for j in range(d+1)]

def coefficient_polynomial(s):
    d=2*s
    sin_over_u=[F((-1)**(j//2)*2**(j+1),factorial(j+1)) if j%2==0 else F(0) for j in range(d+1)]
    B=inverse(sin_over_u,d)
    R=mul(power(B,2*s+1,d),power(even_cos(3,d),2*s,d),d)
    # P_s(N) = [u^(2s)] B(u)^(2s+1) cos(3u)^(2s) cos(Nu).
    coeffs={2*j:R[2*s-2*j]*F((-1)**j,factorial(2*j)) for j in range(s+1)}
    assert coeffs[2*s]==F((-1)**s,2**(2*s+1)*factorial(2*s))
    return coeffs

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('angular_divergence_checks.json'))
    args=parser.parse_args()
    u,N=sp.symbols('u N')
    rows=[];cross_checks=[]
    for s in range(1,7):
        coeffs=coefficient_polynomial(s)
        P=sum(sp.Rational(c.numerator,c.denominator)*N**j for j,c in coeffs.items())
        rows.append({'s':s,'P_s':str(P),'latex':sp.latex(P),'leading_coefficient':str(coeffs[2*s])})
        if s<=3:
            for prime in (5,7):
                phi3=u*sp.cos(3*u)/sp.sin(2*u)
                phiN=-u*sp.sin(prime*sp.pi/2-prime*u)/sp.sin(2*u)
                direct=sp.expand(sp.series(phi3**(2*s)*phiN,u,0,2*s+1).removeO()).coeff(u,2*s)
                expected=-sp.sin(prime*sp.pi/2)*P.subs(N,prime)
                assert sp.simplify(direct-expected)==0
                cross_checks.append({'s':s,'prime':prime,'direct_coefficient':str(direct),'exact_match':True})
    out=args.output
    out.write_text(json.dumps({'meaning':'C_(m3=2s,mN=1) = -sin(N*pi/2) H2^(2s) H_(N-1) P_s(N).',
        'polynomials':rows,'direct_trigonometric_checks':cross_checks,
        'all_leading_coefficients_correct':True},indent=2)+'\n')
    print(json.dumps({'output':str(out),'polynomials':rows,'direct_check_count':len(cross_checks)},indent=2))
if __name__=='__main__':main()
