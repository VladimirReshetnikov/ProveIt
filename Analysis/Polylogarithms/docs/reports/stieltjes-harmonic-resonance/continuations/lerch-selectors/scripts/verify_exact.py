#!/usr/bin/env python3
"""Finite exact checks, not a replacement for the all-order proofs.

Run from any directory. Writes results/exact_checks.json and exact_formulas.json.
"""
from __future__ import annotations
import json
from collections import Counter
from pathlib import Path
import sympy as sp
from selector_algebra import (u,s,lam,frobenius_euler,falling_endpoint,
    endpoint_spectrum,eulerian,negative_polylog,resonance_polynomial,inverse_resonance_series)
ROOT=Path(__file__).resolve().parents[1]
counts=Counter()
def check(family: str, expression: sp.Expr, expected: sp.Expr=sp.Integer(0)) -> None:
    residual=sp.cancel(sp.expand(expression-expected))
    if residual != 0:
        raise AssertionError(f'{family}: residual {residual}')
    counts[family]+=1

def main() -> None:
    # Generating recurrence is independent of the endpoint conditions checked here.
    for z in [sp.Rational(1,3),sp.Rational(-2,3),sp.Integer(-1),sp.I]:
        for n in range(9):
            p=frobenius_euler(n,z)
            cs=endpoint_spectrum(p,z)
            for j,c in enumerate(cs):
                check('Frobenius endpoint jets',c,(1-z)*sp.factorial(n) if j==n else 0)
            if n:
                check('Appell derivatives',sp.diff(p,u),n*frobenius_euler(n-1,z))
    for L in [sp.Integer(1),sp.Integer(2),sp.Integer(3)]:
        for z in [sp.Rational(1,2),sp.Rational(-1,3)]:
            la=z**L
            for n in range(7):
                p=sum((-1)**k*sp.Rational(k+2,k+1)*u**k for k in range(n+1))
                cs=endpoint_spectrum(p,la,L)
                rec=sum(cs[k]*L**k*frobenius_euler(k,la,u).subs(u,u/L)/((1-la)*sp.factorial(k)) for k in range(n+1))
                check('Endpoint reconstruction',rec,p)
    for n in range(1,13):
        p=sp.bernoulli(n,u)
        cs=endpoint_spectrum(p,sp.Integer(1))
        for j,c in enumerate(cs):
            check('Bernoulli resonance jets',c,sp.factorial(n) if j==n-1 else 0)
    for n in range(1,11):
        p=frobenius_euler(n,lam)
        check('Eulerian endpoint formula',p.subs(u,0),(-1)**n*eulerian(n)/(1-lam)**n)
        check('Eulerian factorial value',eulerian(n).subs(lam,1),sp.factorial(n))
        if n>1:
            check('Consecutive Eulerian coprimality',sp.gcd(eulerian(n),eulerian(n-1)),1)
    z=sp.sqrt(3)-2
    p=frobenius_euler(3,z)
    check('Algebraic-twist example',sp.simplify(p-u*(u-1)*(u-(1+sp.sqrt(3))/2)))
    for r in range(2,7):
        n=2*r; p=sp.bernoulli(n,u)-sp.bernoulli(n)
        for z in [sp.Rational(1,3),sp.Integer(-1),sp.Integer(1)]:
            cs=endpoint_spectrum(p,z)
            expected=[j for j in range(2,n+1,2)] if z==-1 else ([n-1] if z==1 else [*range(2,n+1,2),n-1])
            assert sorted(j for j,c in enumerate(cs) if c!=0)==sorted(expected)
            counts['Exact support stratification']+=1
        for z in [sp.Rational(1,3),sp.Integer(-1)]:
            rec=sum(sp.binomial(n,j)*sp.bernoulli(n-j)*frobenius_euler(j,z) for j in range(2,n+1,2))
            rec+=n*(1+z)*frobenius_euler(n-1,z)/(2*(1-z))
            check('Minimal mixing identity',rec,p)
        check('Double endpoint zero',p.subs(u,0))
        check('Double endpoint derivative',sp.diff(p,u).subs(u,0))
        assert sp.diff(p,u,2).subs(u,0)!=0
        counts['No triple endpoint zero']+=1
    # Clear denominators and test every removable-integer numerator.
    for z in [sp.Rational(1,3),sp.Rational(-2,3),sp.Integer(-1)]:
        for d in range(9):
            r=resonance_polynomial(d,z)
            for m in range(1,d+2):
                num=r.subs(s,m)/z-(1-z)*sp.factorial(d)*negative_polylog(d+1-m,z)/z**2
                check('Resonance numerator zeros',num)
    e=sp.Symbol('e')
    for d in range(7):
        for m in range(1,d+2):
            inv=inverse_resonance_series(d,m,4,e)
            den=sp.prod(1+e/sp.Integer(m-k) for k in range(1,d+2) if k!=m)
            for h in range(1,5):
                check('Harmonic resonance compiler',sp.expand(inv*den).coeff(e,h))
    # Low-order Stieltjes and polygamma formulas by exact Laurent algebra.
    E=lambda j:sp.prod(1/(1-e/sp.Integer(k)) for k in range(1,j+1))
    Z1,Z2=sp.symbols('Z1 Z2')
    q=4*E(3)*(sp.Rational(1,120)+Z1*e+Z2*e**2/2)+E(2)-2*E(3)+E(4)
    qs=sp.series(q,e,0,3).removeO().expand()
    check('Printed Stieltjes algebra',qs.coeff(e,0),sp.Rational(1,30))
    check('Printed Stieltjes algebra',qs.coeff(e,1),4*Z1-sp.Rational(1,45))
    check('Printed Stieltjes algebra',-qs.coeff(e,2),-2*Z2-sp.Rational(22,3)*Z1+sp.Rational(5,432))
    raw=-24*e*Z1/falling_endpoint(3)+2/falling_endpoint(2)+12/falling_endpoint(3)+24/falling_endpoint(4)
    constant=sp.series(raw.subs(s,2+e),e,0,1).removeO()
    check('Printed trigamma algebra',constant,-sp.Rational(1,3)-12*Z1)
    # Mutation controls: these are expected nonzero, not successful identities.
    p=frobenius_euler(4,sp.Rational(1,3))
    assert sp.diff(p,u,2).subs(u,1)-sp.diff(p,u,2).subs(u,0)!=0
    counts['Mutation controls rejected']+=1
    assert resonance_polynomial(2,sp.Rational(1,3)).subs(s,1)*3 - (1-sp.Rational(1,3))*sp.factorial(2)*negative_polylog(2,sp.Rational(1,3))*3 !=0
    counts['Mutation controls rejected']+=1
    # Formula tables generated only from the exact recurrence, never PSLQ.
    formulas={'frobenius_at_one_third':{},'euler_gamma_offsets':{},'bernoulli_weights':{},'resonance_polynomials_at_minus_one':{}}
    for n in range(7):
        formulas['frobenius_at_one_third'][str(n)]=str(frobenius_euler(n,sp.Rational(1,3)))
        formulas['resonance_polynomials_at_minus_one'][str(n)]=str(resonance_polynomial(n,sp.Integer(-1)))
    for r in range(1,7):
        n=2*r; rr=resonance_polynomial(n,sp.Integer(-1))
        formulas['euler_gamma_offsets'][str(r)]=str(-sp.diff(rr,s).subs(s,1)/sp.factorial(n))
        formulas['bernoulli_weights'][str(n)]=str(sp.bernoulli(n,u)-sp.bernoulli(n))
    report={'status':'PASS','arithmetic':'exact SymPy rational/polynomial arithmetic', 'sympy_version':sp.__version__,'families':dict(counts),'total_assertions':sum(counts.values()),'scope':'Finite checks only; all-order claims are proved in article.tex.'}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results/exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'results/exact_formulas.json').write_text(json.dumps(formulas,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':
    main()
