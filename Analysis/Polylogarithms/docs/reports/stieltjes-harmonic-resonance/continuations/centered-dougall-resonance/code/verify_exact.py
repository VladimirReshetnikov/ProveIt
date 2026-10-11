#!/usr/bin/env python3
"""Finite exact regression checks; the article supplies all-order proofs."""
from __future__ import annotations
import json
import platform
from pathlib import Path
from collections import Counter
import sympy as s

ROOT=Path(__file__).resolve().parents[1]
counts=Counter()

def check(group: str, expression):
    assert s.expand(expression)==0,(group,expression)
    counts[group]+=1


def rational_A(k,b,c,u,J,jet=False):
    d=1+2*k-b-c
    rs=(k,b-k,c-k,d-u-k)
    L=[s.S(0)]+[-sum(s.bernoulli(2*j+1,r) for r in rs)/(j*(2*j+1)) for j in range(1,J+1)]
    Lp=[s.S(0)]+[s.bernoulli(2*j,rs[-1])/j for j in range(1,J+1)]
    A=[s.S(1)]; Ap=[s.S(0)]
    for j in range(1,J+1):
        A.append(sum(r*L[r]*A[j-r] for r in range(1,j+1))/j)
        Ap.append(sum(r*(Lp[r]*A[j-r]+L[r]*Ap[j-r]) for r in range(1,j+1))/j)
    return (A,Ap) if jet else A


def main():
    x,k,b,c,u=s.symbols('x k b c u')
    for degree in range(1,25):
        check('Bernoulli reflection',s.bernoulli(degree,1-x)-(-1)**degree*s.bernoulli(degree,x))
    rs=(k,b-k,c-k,1+k-b-c-u)
    ell=[s.S(0)]
    for j in range(1,7):
        ell.append(s.Poly(-sum(s.bernoulli(2*j+1,r) for r in rs)/(j*(2*j+1)),k,b,c,u).as_expr())
        E=s.diff(ell[-1],u)-s.diff(ell[-1],k)-s.diff(ell[-1],b)-s.diff(ell[-1],c)
        check('Generic differential law for logarithms',E-s.bernoulli(2*j,k)/j)
    A=[s.S(1)]
    for j in range(1,4):
        A.append(s.Poly(sum(r*ell[r]*A[j-r] for r in range(1,j+1))/j,k,b,c,u).as_expr())
        E=s.diff(A[j],u)-s.diff(A[j],k)-s.diff(A[j],b)-s.diff(A[j],c)
        check('Generic coefficient differential law',E-sum(s.bernoulli(2*r,k)/r*A[j-r] for r in range(1,j+1)))
        R=(-1)**j*s.rf(1+2*k-b-c,j)*s.rf(1-b,j)*s.rf(1-c,j)/s.factorial(j)
        check('Generic residue polynomial',A[j].subs(u,-j)-R)
    params=[(s.Rational(1,2),s.Rational(1,2),s.Rational(1,2)),
            (s.Rational(3,4),s.Rational(2,3),s.Rational(4,5)),
            (s.Rational(5,4),s.S(1),s.Rational(3,4)),
            (s.S(2),s.S(2),s.S(1)),
            (s.Rational(7,6),s.Rational(1,3),s.Rational(5,7)),
            (s.Rational(9,5),s.Rational(7,4),s.Rational(6,5))]
    rows=[]
    for kv,bv,cv in params:
        for N in range(11):
            av,ap=rational_A(kv,bv,cv,-N,N,True)
            R=(-1)**N*s.rf(1+2*kv-bv-cv,N)*s.rf(1-bv,N)*s.rf(1-cv,N)/s.factorial(N)
            check('Rational residue polynomial',av[N]-R)
            # D=d_k+d_b+d_c fixes d0. Differentiate the other two polynomial factors.
            bb,cc=s.symbols('bb cc')
            DR=(-1)**N*s.rf(1+2*kv-bv-cv,N)/s.factorial(N)
            DR*=s.diff(s.rf(1-bb,N)*s.rf(1-cc,N),bb)+s.diff(s.rf(1-bb,N)*s.rf(1-cc,N),cc)
            DR=DR.subs({bb:bv,cc:cv})
            check('Rational finite-part cancellation',ap[N]-DR-sum(s.bernoulli(2*r,kv)/r*av[N-r] for r in range(1,N+1)))
            rows.append({'kappa':str(kv),'b':str(bv),'c':str(cv),'N':N,'rho':str(R),'A_N_prime':str(ap[N])})
    half=s.Rational(1,2)
    y=s.symbols('y')
    for N in range(13):
        poly=s.Poly(s.prod(1-(r-half)**2*y for r in range(1,N+1)),y)
        av=rational_A(half,half,half,-N,N+3)
        for j in range(N+4):
            check('Integer half-parameter truncations',av[j]-poly.nth(j))
        poly=s.Poly(s.prod(1-r*r*y for r in range(1,N+1)),y)
        av=rational_A(half,half,half,-N-half,N+3)
        for j in range(N+4):
            check('Half-integer half-parameter truncations',av[j]-poly.nth(j))
    av,ap=rational_A(half,half,half,u,2,True)
    check('Printed A1',av[1]-u*(4*u*u-1)/12)
    check('Printed A1 prime',ap[1].subs(u,-1)-s.Rational(11,12))
    check('Printed revived-head coefficient',s.S(2)-s.Rational(11,6)-s.Rational(1,6))
    # The derivative law of the normalized zeta primitive follows by coefficient matching.
    for j in range(1,21):
        check('Normalized primitive cancellation',s.harmonic(j)-1/s.S(j)-s.harmonic(j-1))
    # Universal polynomial-weighted telescoping in independent formal symbols P_j.
    for degree in range(13):
        pol=sum((r+1)*x**r for r in range(degree+1))
        P=s.symbols('P0:'+str(degree+1))
        psi=s.symbols('psi')
        expr=s.S(0)
        for j in range(degree+1):
            expr+=(-1)**j*(s.diff(pol,x,j+1)*P[j]+s.diff(pol,x,j)*(psi if j==0 else P[j-1]))
        check('Polynomial primitive telescope',expr-pol*psi)
    # Order conversion factors: d/du zeta(s+2u) and the pole residue 1/2.
    t=s.symbols('t')
    check('Doubled-excess pole',s.residue(1/(2*t),t,0)-s.Rational(1,2))
    # Independent ordinary exponential coefficient generation for the half-parameter table.
    av=rational_A(half,half,half,s.Rational(-2,3),8)
    lv=[s.S(0)]
    rs=(half,0,0,half+s.Rational(2,3))
    for j in range(1,9): lv.append(-sum(s.bernoulli(2*j+1,r) for r in rs)/(j*(2*j+1)))
    # Truncated product of exp(l_j*y^j), using exact finite polynomials.
    e=s.Poly(1,y)
    for j in range(1,9):
        f=s.Poly(sum(lv[j]**q*y**(j*q)/s.factorial(q) for q in range(8//j+1)),y)
        prod=e*f
        e=s.Poly.from_dict({mon:coef for mon,coef in prod.terms() if mon[0]<=8},y)
    for j in range(9): check('Independent exponential coefficients',av[j]-e.nth(j))
    for p in range(2,13):
        Z=s.symbols('Z0:'+str(p+2))
        weighted=sum(s.Rational(p-j,p-1)*Z[j]*Z[p+1-j] for j in range(2,p))
        check('Euler-primitive product symmetrization',weighted-s.Rational(1,2)*sum(Z[j]*Z[p+1-j] for j in range(2,p)))
    out={'status':'PASS','total_assertions':sum(counts.values()),'groups':dict(counts),
         'python':platform.python_version(),'sympy':s.__version__,
         'scope':'Finite exact regression assertions, not a proof-assistant formalization.'}
    (ROOT/'results'/'exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    (ROOT/'results'/'residue_table.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
