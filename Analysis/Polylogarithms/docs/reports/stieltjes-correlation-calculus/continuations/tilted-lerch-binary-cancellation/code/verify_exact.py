#!/usr/bin/env python3
"""Finite exact checks for Tilted Lerch Convolutions.

These checks verify algebraic interfaces and examples. Infinite analytic
identities are proved in article.tex; a finite replay is not their proof.
"""
from __future__ import annotations
import itertools
import json
import math
import platform
import time
from collections import Counter
from pathlib import Path
from fractions import Fraction as Q
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter[str] = Counter()

def check(condition: bool, family: str) -> None:
    if not bool(condition):
        raise AssertionError(f"Failed exact check: {family}")
    COUNTS[family] += 1

def cweights(nodes: tuple[int, ...]) -> list[Q]:
    return [Q(1, math.prod(m - n for m in nodes if m != n)) for n in nodes]

def cancellation(nodes: tuple[int, ...]) -> Q:
    return sum((c * (-1)**n for c, n in zip(cweights(nodes), nodes)), Q(0))

def binomial_coeffs(orders, shifts, nmax):
    ans = [sp.S.One]
    for n in range(1, nmax + 1):
        ans.append(sp.expand(sum((-1)**k * sum(s*d**k for s,d in zip(orders,shifts)) * ans[n-k]
                                 for k in range(1,n+1))/n))
    return ans

def main() -> None:
    start = time.time()
    x,z,D,P,k,s = sp.symbols('x z D P k s')
    # Collision operators, with P standing for pi^2, avoid approximate pi.
    for r in range(1,15):
        u = sp.symbols('u')
        raw = sp.expand(sp.prod(D + 2*sp.I*u*(sp.Rational(r-2,2)-j) for j in range(r-1)))
        if r % 2:
            m = (r-1)//2
            expected = sp.prod(D**2 + (2*j-1)**2*u**2 for j in range(1,m+1))
        else:
            m=r//2
            expected = D*sp.prod(D**2+4*j*j*u*u for j in range(1,m))
        check(sp.expand(raw-expected)==0, 'central_collision_operator')
    # Ordinary and Hermite divided-difference coefficient extraction.
    for r in range(2,9):
        nodes=list(range(1,r+1))
        for power in range(r+3):
            dd=sum(sp.Rational(v**power, math.prod(v-w for w in nodes if w!=v)) for v in nodes)
            rem=sp.rem(x**power,sp.prod(x-v for v in nodes),x)
            check(dd==sp.Poly(rem,x).coeff_monomial(x**(r-1)), 'divided_difference_polynomial')
    for multiplicities in [(2,1),(2,2),(3,1),(1,2,1),(2,1,2)]:
        nodes=[sp.Integer(j+1) for j in range(len(multiplicities))]
        total=sum(multiplicities)
        for power in range(total+3):
            herm=0
            for v,m in zip(nodes,multiplicities):
                other=sp.prod((x-w)**n for w,n in zip(nodes,multiplicities) if w!=v)
                herm+=sp.diff(x**power/other,x,m-1).subs(x,v)/sp.factorial(m-1)
            poly=sp.prod((x-v)**m for v,m in zip(nodes,multiplicities))
            check(sp.simplify(herm-sp.Poly(sp.rem(x**power,poly,x),x).coeff_monomial(x**(total-1)))==0,
                  'Hermite_divided_difference')
    # Binomial recurrence versus direct finite convolution.
    for orders, shifts in [([sp.Rational(2,3),sp.Rational(-4,5)],[sp.Rational(1,4),sp.Rational(-1,3)]),
                           ([2,-2,sp.Rational(3,2)],[0,sp.Rational(2,5),sp.Rational(-1,5)]),
                           ([s,2],[sp.Rational(1,3),sp.Rational(-1,2)])]:
        B=binomial_coeffs(orders,shifts,10)
        direct=[sp.S.One]+[sp.S.Zero]*10
        for order,shift in zip(orders,shifts):
            series=[(-1)**n*sp.rf(order,n)*shift**n/sp.factorial(n) for n in range(11)]
            direct=[sp.expand(sum(direct[j]*series[n-j] for j in range(n+1))) for n in range(11)]
        for n in range(11):
            check(sp.expand(B[n]-direct[n])==0,'anchor_recurrence')
    h,t=sp.symbols('h t')
    B=binomial_coeffs([s,-2,-1],[0,h,t],8)
    expected=[1,2*h+t,h*h+2*h*t,h*h*t]+[0]*5
    for lhs,rhs in zip(B,expected): check(sp.expand(lhs-rhs)==0,'finite_anchor_closure')
    # Logarithmic source-order coefficients and Bell--harmonic formula.
    for m in range(1,5):
        for n in range(0,8):
            poly=sp.expand_func(sp.rf(s,n))
            logs=[(-1)**(j-1)*sp.factorial(j-1)*sum(sp.Rational(1,q**j) for q in range(m,m+n))
                  for j in range(1,5)]
            bells=[sp.S.One, logs[0],logs[0]**2+logs[1],
                   logs[0]**3+3*logs[0]*logs[1]+logs[2],
                   logs[0]**4+6*logs[0]**2*logs[1]+3*logs[1]**2+4*logs[0]*logs[2]+logs[3]]
            for ell in range(5):
                check(sp.diff(poly,s,ell).subs(s,m)==sp.rf(m,n)*bells[ell], 'Pochhammer_Bell_harmonic')
    for m in range(-4,1):
        for n in range(8):
            poly=sp.Poly(sp.expand_func(sp.rf(s,n)),s)
            # Unsigned first-kind Stirling numbers are recovered by polynomial coefficients.
            from sympy.functions.combinatorial.numbers import stirling
            for ell in range(4):
                direct=sum(stirling(n,j,kind=1)*sp.factorial(j)/sp.factorial(j-ell)*sp.Integer(m)**(j-ell)
                           for j in range(ell,n+1))
                check(sp.diff(poly.as_expr(),s,ell).subs(s,m)==direct,'Pochhammer_zero_safe')
    # Raw-moment operator: induction coefficients, without commuting through s-shifts incorrectly.
    for n in range(0,9):
        for ell in range(n+2):
            def coeff(n,l):
                return sp.binomial(n,l)*sp.rf(s,l) if 0<=l<=n else sp.S.Zero
            lhs=coeff(n,ell)+(s+ell-1)*coeff(n,ell-1)
            rhs=coeff(n+1,ell)
            check(sp.simplify(lhs-rhs)==0,'raw_moment_operator')
    # Repeated primitive resonance factor.
    for depth in range(1,10):
        denom=sp.prod(s-j for j in range(1,depth+1))
        for ell in range(1,depth+1):
            actual=(-1)**depth/sp.diff(denom,s).subs(s,ell)
            expected=sp.Rational((-1)**ell,math.factorial(ell-1)*math.factorial(depth-ell))
            check(actual==expected,'anchored_primitive_resonance')
    # The full modular-inverse test is checked on distinct node sets, with exact fractions.
    modular_samples=0
    for r, ceiling in [(3,10),(5,9),(7,10),(9,10)]:
        for tail in itertools.combinations(range(1,ceiling+1),r-1):
            nodes=(0,)+tail
            E=sp.prod(x-n for n in nodes if n%2==0)
            O=sp.prod(x-n for n in nodes if n%2)
            e=sum(n%2==0 for n in nodes); o=r-e
            sval=cancellation(nodes)
            if not o:
                check(sval==0,'equal_parity_cancellation'); continue
            U=sp.invert(E,O,x)
            top=sp.Poly(U,x).coeff_monomial(x**(o-1))
            check(sp.Rational(sval.numerator,sval.denominator)==2*(-1)**r*top,'inverse_polynomial_criterion')
            half=sval/2
            check(half.denominator%2==1,'odd_denominator_integrality')
            check((half.numerator%2)==(math.comb(r-2,o-1)%2),'binary_obstruction')
            if r-1 & (r-2)==0:
                check(sval!=0,'power_of_two_depth_classification')
            modular_samples+=1
    # The general mixed-parity family has an identity in Q[k,x], not just samples.
    E=x*(x-2)*(x-2*k)*(x-2*k-4)
    O=(x-1)*(x-2*k-1)*(x-2*k-3)
    denominator=3*(2*k-1)*(2*k+1)*(2*k+3)
    unumer=2*x-6*k-5
    vnumer=2*x*x-(6*k+7)*x+6*k-3
    check(sp.expand(E*unumer-denominator-O*vnumer)==0,'symbolic_mixed_family_Bezout')
    for kval in range(2,52):
        nodes=(0,1,2,2*kval,2*kval+1,2*kval+3,2*kval+4)
        check(cancellation(nodes)==0,'mixed_family_exact_samples')
        for dil,translate in [(3,0),(5,7)]:
            check(cancellation(tuple(dil*n+translate for n in nodes))==0,'affine_mixed_family_samples')
    nodes=(0,1,2,4,5,7,8)
    c=cweights(nodes)
    expectedc=[Q(1,2240),Q(-1,504),Q(1,360),Q(-1,288),Q(1,360),Q(-1,1260),Q(1,4032)]
    check(c==expectedc,'explicit_depth_seven_weights')
    check(sp.cancel(sum(sp.Rational(v.numerator,v.denominator)/(x+n) for v,n in zip(c,nodes))-
                    1/sp.prod(x+n for n in nodes))==0,'explicit_partial_fraction')
    Bpoly=sp.Poly(sp.prod(x*x+(2*j-1)**2*P for j in range(1,4)),x)
    value=0
    harmonic_sums=[]
    for j in range(4):
        q=2*j+1
        H=sum(cv*(-1)**n*sum((Q((-1)**(i-1),i**q) for i in range(1,n+1)),Q(0)) for cv,n in zip(c,nodes))
        harmonic_sums.append(str(H))
        value-=Bpoly.coeff_monomial(x**(2*j))*sp.factorial(2*j)*sp.Rational(H.numerator,H.denominator)/sp.factorial(6)
    target=sp.Rational(11,516096)*P**3+sp.Rational(1138070753,5852528640000)*P**2+sp.Rational(31111437326981,68825736806400000)*P+sp.Rational(24335931370253514869,56657346539028480000000)
    check(sp.expand(value-target)==0,'explicit_six_dimensional_integral')
    # Negative controls reject exact mutations rather than merely matching positives.
    check(sp.expand(E*(unumer+1)-denominator-O*vnumer)!=0,'negative_control_Bezout_mutation')
    bad=c.copy();bad[0]=-bad[0]
    check(sum(v*(-1)**n for v,n in zip(bad,nodes))!=0,'negative_control_residue_sign')
    check(cancellation((0,1,2,3,4,5,6))!=0,'negative_control_mixed_nonvanishing')
    check(sp.expand((2*h+t)-(h+t))!=0,'negative_control_anchor_coefficient')
    result={'status':'PASS','scope':'finite exact algebra; not proof-assistant formalization',
            'assertions':sum(COUNTS.values()),'families':dict(COUNTS),'modular_sets_tested':modular_samples,
            'depth_seven_nodes':list(nodes),'depth_seven_weights':[str(v) for v in c],
            'alternating_harmonic_sums_q_1_3_5_7':harmonic_sums,
            'depth_seven_polynomial_in_pi_squared':str(target),
            'sympy_version':sp.__version__,'python_version':platform.python_version(),
            'elapsed_seconds':round(time.time()-start,3)}
    (ROOT/'data'/'exact_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
