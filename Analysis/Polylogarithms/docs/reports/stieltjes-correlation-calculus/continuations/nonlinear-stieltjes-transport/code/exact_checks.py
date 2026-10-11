#!/usr/bin/env python3
"""Exact finite checks with independent cutoff primitives and cocycle tests.
This is a regression suite, not proof-assistant formalization of the theorems.
"""
import json, sys, time
from pathlib import Path
from fractions import Fraction as Q
from math import factorial, comb
import sympy as sp
from jets import *
ROOT=Path(__file__).resolve().parents[1]
checks=[]

def check(name,lhs,rhs=0):
    d=sp.expand(lhs-rhs)
    ok=d==0
    checks.append({'name':name,'passed':bool(ok)})
    if not ok: raise AssertionError(f'{name}: difference {d}')

def cutoff_contact(phi,k,n,h,log_slope):
    """Independent constant term of an elementary cutoff antiderivative.
    Expand h(phi^-1(x)), integrate x^-k log^n x term by term, then put x=phi(y).
    Only the singular head can supply a constant term.
    """
    r=phi[1:]+[0]; L=logarithm(r,log_slope)
    test=compose(h,reverse(phi)); total=0
    for j in range(k):
        a=j-k+1
        if a==0:
            term=divide(power(L,n+1)[0],n+1)
        else:
            poly=constant(0,len(phi)-1)
            for ell in range(n+1):
                c=Q((-1)**ell*factorial(n),factorial(n-ell)*a**(ell+1))
                poly=add(poly,scale(power(L,n-ell),c))
            term=mul(power(r,a),poly)[-a]
        total+=test[j]*term
    return sp.expand(total)

def main():
    start=time.time(); N=8; one=constant(Q(1),N)
    maps=[ [Q(0),Q(1),Q(1,3),Q(-1,5),Q(1,7)]+[Q(0)]*4,
           [Q(0),Q(1),Q(0),Q(2,5),Q(0),Q(-1,9)]+[Q(0)]*3,
           [Q(0),Q(2),Q(-1,4),Q(1,6),Q(1,11)]+[Q(0)]*4 ]
    L=sp.Symbol('L')
    for mi,phi in enumerate(maps):
        ell=0 if phi[1]==1 else L
        for k in range(1,6):
            for n in range(4):
                for j in range(k):
                    h=constant(Q(0),N); h[j]=Q(1)
                    check(f'cutoff-map{mi}-k{k}-n{n}-test{j}',
                        contact_monomial(phi,k,n,h,ell),cutoff_contact(phi,k,n,h,ell))
    # Cocycle tested by an independent singular expansion of the pulled-back density.
    phi,psi=maps[:2]; composite=compose(phi,psi); psinv=reverse(psi)
    for k in range(1,6):
        r=phi[1:]+[0]; lp=logarithm(r); a=mul(derivative(phi),power(r,-k))
        for n in range(3):
            for j in range(k):
                h=constant(Q(0),N); h[j]=Q(1)
                rhs=contact_monomial(phi,k,n,compose(h,psinv))
                for ell in range(n+1):
                    co=scale(mul(a,power(lp,n-ell)),comb(n,ell))
                    for v in range(k): rhs+=co[v]*contact_monomial(psi,k-v,ell,h)
                check(f'cocycle-k{k}-n{n}-test{j}',contact_monomial(composite,k,n,h),rhs)
    # Pullback of a delta derivative: inverse jets versus the Lagrange formula.
    for mi,phi in enumerate(maps):
        tau=reverse(phi); ratio=phi[1:]+[0]
        for d in range(7):
            for j in range(d+1):
                lhs=(-1)**d*factorial(d)*power(tau,j)[d]
                if d==0: rhs=1
                elif j==0: rhs=0
                else:
                    coefficient=(-1)**(d+j)*Q(factorial(d-1),factorial(j-1))*power(ratio,-d)[d-j]
                    rhs=coefficient*(-1)**j*factorial(j)
                check(f'delta-transport-map{mi}-d{d}-test{j}',lhs,rhs)
    # Singular derivative polynomial and the compact Stieltjes contact formula.
    x,u=sp.symbols('x u',positive=True)
    for p in range(7):
        e=elementary(p); P=sum(e[j]*u**j for j in range(p+1))
        check(f'harmonic-product-p{p}',P,sp.prod(1+u/sp.Integer(j) for j in range(1,p+1)))
        for m in range(5):
            singular=sum((-1)**(p+j)*factorial(p)*Q(factorial(m),factorial(m-j))*e[j]*x**(-p-1)*sp.log(x)**(m-j) for j in range(min(m,p)+1))
            check(f'stieltjes-derivative-p{p}-m{m}',singular,sp.diff(sp.log(x)**m/x,x,p))
            phi=maps[0]
            rhs=sum((-1)**(p+j)*factorial(p)*Q(factorial(m),factorial(m-j))*e[j]*contact_monomial(phi,p+1,m-j,one) for j in range(min(m,p)+1))
            check(f'stieltjes-contact-p{p}-m{m}',contact_stieltjes(phi,m,p,one),rhs)
        if p:
            for m in range(2*p,2*p+3):
                for j in range(p+1):
                    h=constant(Q(0),N); h[j]=Q(1)
                    check(f'tangent-vanishing-p{p}-m{m}-test{j}',contact_stieltjes(maps[0],m,p,h))
    for p in range(1,7):
        check(f'sharp-tangent-threshold-p{p}',contact_stieltjes(maps[0],2*p-1,p,one),Q(factorial(2*p-1),factorial(p))*Q(1,3)**p)
    a,b=sp.symbols('a b'); phi=[Q(0),Q(1),a,b]+[Q(0)]*(N-3)
    h0=one; h1=constant(Q(0),N); h1[1]=Q(1)
    check('gamma0prime-delta',contact_stieltjes(phi,0,1,h0),-a)
    check('gamma0second-delta',contact_stieltjes(phi,0,2,h0),2*b-3*a*a)
    check('gamma0second-delta-prime',contact_stieltjes(phi,0,2,h1),2*a)
    check('square-contact',contact_monomial(phi,2,0,h0),a)
    check('cube-leading-contact',contact_monomial(phi,3,0,h0),b-Q(3,2)*a*a)
    # A deliberately incorrect slope-only prescription must be rejected.
    assert contact_stieltjes(maps[0],0,1,one)!=0
    checks.append({'name':'negative-control-slope-only','passed':True})
    # The interval Mobius scalar formula, with independent polynomial coefficient extraction.
    z,l=sp.symbols('z l')
    for p in range(1,6):
        ep=elementary(p); em=elementary(p-1)
        Pp=sum(ep[j]*(-u)**j for j in range(p+1)); Pm=sum(em[j]*(-u)**j for j in range(p))
        for m in range(5):
            # coefficient [z^p] (1+z)^(p-1) T(log lambda-log(1+z)).
            zr=[Q(1),Q(1)]+[Q(0)]*(N-1)
            logz=logarithm(zr,l); logz=[l]+[-v for v in logz[1:]]
            lhs=mul(power(zr,p-1),t_polynomial(m,p,logz))[p]
            rhs=-Q(factorial(m),p)*sp.expand(Pp*Pm*sum(l**j*u**j/sp.factorial(j) for j in range(m+1))).coeff(u,m)
            check(f'mobius-binomial-p{p}-m{m}',lhs,rhs)
    out={'kind':'exact rational/polynomial regression assertions','count':len(checks),'passed':all(q['passed'] for q in checks),'elapsed_seconds':round(time.time()-start,3),'python':sys.version,'sympy':sp.__version__,'checks':checks}
    (ROOT/'data/exact_checks.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
if __name__=='__main__': main()
