#!/usr/bin/env python3
"""Regression tests are supplementary; the all-n proofs are in the article."""
from pathlib import Path
from fractions import Fraction
from math import gcd,lcm,prod
import json
import random
from factorial_divisibility import A,B,Factor,Ratio,classify,effective_bound,height_one_denominators,vp

ROOT=Path(__file__).resolve().parents[1]


def need(ok, label):
    if not ok:raise AssertionError(label)


def main():
    count={'step_identity_tests':0,'direct_fraction_tests':0,'valuation_tests':0,
           'uniform_family_tests':0,'large_index_valuation_tests':0,'classification_tests':0,
           'recurrence_and_asymptotic_tests':0}
    # Check an independent table evaluation against the general floor definition.
    for r,divs in [(A,(2,3,5)),(B,(2,3,4))]:
        L=r.grid
        for q in range(2,301):
            for n in range(q):
                j=L*n//q
                need(r.delta(Fraction(n,q))==j-sum(j//d for d in divs),'floor grid')
                count['step_identity_tests']+=1
    configurations=[(A,(2,),7),(A,(3,),1),(A,(5,),1),(A,(2,3,5),42),
                    (B,(1,),385),(B,(2,),5),(B,(3,),1),(B,(1,2,3),770)]
    for r,ks,C in configurations:
        for n in range(101):
            value=C*r.value(n)/prod(k*n+1 for k in ks)
            need(value.denominator==1,'direct sharp divisibility')
            count['direct_fraction_tests']+=1
        for n in range(10001):
            for p in [2,3,5,7,11,13]:
                val=r.valuation(n,p)+vp(C,p)-sum(vp(k*n+1,p) for k in ks)
                need(val>=0,'sharp valuation')
                count['valuation_tests']+=1
    # Direct checks of the explicit all-r multipliers in the main result.
    for k in [2,3,5]:
        for rmax in range(1,13):
            indices=[i for i in range(1,rmax+1) if gcd(i,k)==1]
            bound=30*rmax//k
            C=lcm(*range(1,bound+1))**len(indices)
            for n in range(41):
                value=C*A.value(n)/prod(k*n+i for i in indices)
                need(value.denominator==1,'positive all-r family')
                count['uniform_family_tests']+=1
    for r in [A,B]:
        M=r.maximum
        for rmax in range(1,31):
            indices=[i for i in range(1,rmax+1) if gcd(i,M)==1]
            C=lcm(*range(1,rmax+1))**len(indices)
            for n in range(31):
                value=C*r.value(n)/prod(M*n-i for i in indices)
                need(value.denominator==1,'negative all-r family')
                count['uniform_family_tests']+=1
    need(height_one_denominators(A)==([1,2,3,5],[30]),'A classification')
    need(height_one_denominators(B)==([1,2,3],[12]),'B classification')
    for k in range(1,61):
        for b in [-11,-7,-1,1,7,11]:
            if gcd(k,b)!=1:continue
            good=(k in [1,2,3,5]) if b>0 else k==30
            need(classify(A,(Factor(k,b),))==good,'general one-sided criterion')
            need(not classify(A,(Factor(k,b,2),)),'squared factor obstruction')
            count['classification_tests']+=2
    # A genuine height-two example permits squared factors.
    doubled=Ratio(A.numerator*2,A.denominator*2)
    need(classify(doubled,(Factor(2,1,2),)),'height-two capacity')
    need(not classify(doubled,(Factor(2,1,3),)),'height-two excess')
    rng=random.Random(20260919)
    for r,ks,C in configurations:
        for _ in range(100):
            n=rng.getrandbits(256)
            for p in [2,3,5,7,11]:
                need(r.valuation(n,p)+vp(C,p)>=sum(vp(k*n+1,p) for k in ks),'large n')
                count['large_index_valuation_tests']+=1
    # Explicit infinite obstruction family: n=(3*p-1)/4, p=3 mod 4, p>30.
    for p in [31,43,47,59,67,71,79,83,103,107]:
        n=(3*p-1)//4
        need(A.valuation(n,p)==0 and (4*n+1)%p==0,'inadmissible slope witness')
    # Known negative factors, checked exactly (including n=0).
    for r in [A,B]:
        for n in range(101):
            need((r.value(n)/(r.maximum*n-1)).denominator==1,'known first negative factor')
    # Exact hypergeometric recurrence checks; no floating-point gamma evaluation.
    alpha=tuple(Fraction(a,30) for a in (1,7,11,13,17,19,23,29))
    beta=tuple(Fraction(a,b) for a,b in ((1,2),(1,3),(2,3),(1,5),(2,5),(3,5),(4,5)))
    beta_shifted=tuple(Fraction(a,b) for a,b in ((3,2),(4,3),(2,3),(6,5),(2,5),(3,5),(4,5)))
    lam=2**14*3**9*5**5
    for n in range(100):
        a0,a1=A.value(n),A.value(n+1)
        need((n+1)*prod(n+b for b in beta)*a1==lam*prod(n+a for a in alpha)*a0,
             'A hypergeometric recurrence')
        u0=42*a0/prod(k*n+1 for k in (2,3,5))
        u1=42*a1/prod(k*(n+1)+1 for k in (2,3,5))
        need((n+1)*prod(n+b for b in beta_shifted)*u1==lam*prod(n+a for a in alpha)*u0,
             'U hypergeometric recurrence')
        count['recurrence_and_asymptotic_tests']+=2
    sigma1=(sum(Fraction(1,a) for a in A.numerator)-sum(Fraction(1,b) for b in A.denominator))/12
    S1=sum(Fraction(1,k) for k in (2,3,5))
    S2=sum(Fraction(1,k*k) for k in (2,3,5))
    need(sigma1==Fraction(7,120) and sigma1-S1==Fraction(-39,40),'first asymptotic coefficient')
    need(((sigma1-S1)**2+S2)/2==Fraction(3893,5760),'second asymptotic coefficient')
    sigma1B=(sum(Fraction(1,a) for a in B.numerator)-sum(Fraction(1,b) for b in B.denominator))/12
    need(sigma1B==Fraction(1,36),'B asymptotic coefficient')
    count['recurrence_and_asymptotic_tests']+=3
    report={'status':'PASS','random_seed':20260919,'checks':count,
            'note':'Finite tests supplement, and do not replace, the all-n theorem and exact certificates.'}
    (ROOT/'data'/'test_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
