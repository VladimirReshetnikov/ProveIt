#!/usr/bin/env python3
"""Independent exact checks. Requires SymPy; does not use numerical root finding."""
from __future__ import annotations
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
import sympy as sp
from coefficients import generate, j, r


def ordered_stirling_row(m: int) -> list[int]:
    if m < 0:
        raise ValueError('m must be nonnegative')
    a = [1]
    for h in range(1,m+1):
        a = [0]+[k*((a[k] if k<len(a) else 0)+a[k-1]) for k in range(1,h+1)]
    return a


def main():
    P, C, L = generate(4)
    x, eps = sp.symbols('x eps')
    coefficient_checks = 0
    for defect in range(17):
        if defect == 0:
            dj = sp.Integer(1)
        else:
            pts = [(m,sp.Rational(ordered_stirling_row(m)[m-defect],factorial(m)))
                   for m in range(defect+1,2*defect+2)]
            dj = sp.interpolate(pts,x)
        normalized = sp.expand(sp.factorial(defect)*(2*eps)**defect*dj.subs(x,1/eps))
        # This side is independently reconstructed from exact Stirling values.
        tilt = sp.exp(-r*sum(sp.Rational(defect**(h+1),h+1)*eps**h for h in range(1,5)))
        q = sp.series(normalized*tilt,eps,0,5).removeO().expand()
        for h in range(5):
            assert sp.expand(q.coeff(eps,h)-P[h].subs(j,defect)) == 0
            coefficient_checks += 1
    root_checks=0
    for m in range(1,11):
        T=ordered_stirling_row(m)
        for n in [0,1,2,5,20]:
            poly=sp.Poly(sum(T[k]*k**n*x**(k-1) for k in range(1,m+1)),x)
            assert poly.count_roots(-1,0)==m-1
            assert sp.gcd(poly,poly.diff()).degree()==0
            root_checks+=1
    moment_checks=0
    for m in range(2,19):
        T=ordered_stirling_row(m)
        for n in range(16):
            W=[T[m-d]*(m-d)**n for d in range(m)]
            total=sum(W)
            mu=Fraction(sum(d*w for d,w in enumerate(W)),total)
            var=Fraction(sum(d*d*w for d,w in enumerate(W)),total)-mu*mu
            theta=Fraction(W[1],W[0])
            e2=Fraction(W[2],W[0]) if m>2 else Fraction(0)
            delta=theta*theta-2*e2
            B=Fraction(n, (m-1)**2)+Fraction(5*m-7,3*(m-1)**2)
            assert 0<=delta<=theta*theta*B
            assert theta/2<=mu<=theta
            assert theta/4<=var<=theta
            assert theta-mu<=delta and theta-var<=2*delta
            moment_checks+=1
    prefix=[1,1,9,211,9285,658171,68504709,9837380491,1863598406805,
            450247033371451,135111441590583909,49300373690091496171,
            21495577955682021043125,11037123350952586270549531,
            6591700149366720366704735109]
    for n,target in enumerate(prefix):
        T=ordered_stirling_row(n)
        assert sum(k**n*T[k] for k in range(n+1))==target
    # Two explicitly printed inverse coefficients have zero formal residual through eps^2.
    from coefficients import inverse_first_two, lam
    beta,ell,d0,d1=inverse_first_two(L)
    delta_r=d0*eps+d1*eps**2
    ll=beta*(1-delta_r+delta_r**2/2)
    residual=ll+eps*L[1].subs({lam:ll,r:ell+delta_r})+eps**2*L[2].subs({lam:ll,r:ell+delta_r})-beta
    assert all(sp.expand(residual).coeff(eps,h).expand()==0 for h in range(3))
    report={'status':'PASS','exact_coefficient_identities':coefficient_checks,
            'exact_Sturm_root_counts':root_checks,'exact_moment_bound_instances':moment_checks,
            'OEIS_prefix_values':len(prefix),'inverse_formal_orders':2,
            'sympy_version':sp.__version__,
            'scope':'Finite checks only; the manuscript contains the general proofs.'}
    root=Path(__file__).resolve().parents[1]
    (root/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
