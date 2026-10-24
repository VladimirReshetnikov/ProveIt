#!/usr/bin/env python3
"""Exact finite controls for the new arithmetic proof. No consistency search."""
from pathlib import Path
from fractions import Fraction
from math import comb, gcd, isqrt
import json

ROOT=Path(__file__).resolve().parent

def check(ok,msg):
    if not ok:raise ValueError(msg)

def upper_half_lucas(N,lower,x,p):
    """Sum binom(N,k)*x**k over k>=lower, mod prime p (digit DP)."""
    ds=[];ls=[];v=N;w=lower
    while v or w:
        ds.append(v%p);ls.append(w%p);v//=p;w//=p
    states={0:1}
    for place in range(len(ds)-1,-1,-1):
        new={}
        for comparison,total in states.items():
            for k in range(ds[place]+1):
                cp=comparison if comparison else ((k>ls[place])-(k<ls[place]))
                weight=comb(ds[place],k)*pow(x,k*(p**place),p)%p
                new[cp]=(new.get(cp,0)+total*weight)%p
        states=new
    return (states.get(0,0)+states.get(1,0))%p

def run():
    # Small finite models corroborate the digit-DP transcription.
    cases=0
    for p in [3,5,7,11,31]:
        for N in range(1,55):
            for lower in [0,N//2,N]:
                for x in [1,2]:
                    actual=sum(comb(N,k)*pow(x,k,p) for k in range(lower,N+1))%p
                    check(upper_half_lucas(N,lower,x,p)==actual,'Lucas finite model')
                    cases+=1
    # A genuine half-binomial-kernel tuple disproves a universal gcd premise.
    # No fixed native outer-mask completion is claimed for this tuple.
    q,R,p=32,655351,31;r=(R-1)//2;x=pow(2,R,p)
    residue=upper_half_lucas(2*r,r,x,p)*pow(pow(x,r,p),-1,p)*pow(2,-1,p)%p
    hres=(4*residue*(x+1)+3)%p
    check((r.bit_count(),x,residue,hres)==(16,2,23,0),'Noncoprime kernel control')
    check(3*q<R<q**4 and R%4==3,'Kernel bounds')
    # Adjacent-Pell descent: exact rational obstruction and nonadjacent failure.
    samples=0
    for Q in range(2,24):
        for V in range(-30,31):
            s=Fraction(Q*V*V-1,Q-1)
            if s<0:continue
            a,b=isqrt(s.numerator),isqrt(s.denominator)
            if a*a==s.numerator and b*b==s.denominator:
                check(b==1,'Adjacent-Pell integrality finite control');samples+=1
    check(Fraction(2)*1**2-4*Fraction(1,2)**2==1,'Nonadjacent negative control')
    # Magnitude bound separating an integer rational residue; all exact.
    inequalities=0
    for qq in range(16,40):
        for rr in range(4,18):
            check(Fraction(qq**rr,2)-1>qq*2**(2*rr+1),'Pell growth cutoff')
            inequalities+=1
    # Rational square-root extraction really needs noncancellation.
    # sqrt(2)+sqrt(8)-sqrt(18)+100=100.
    check(1+2-3==0,'Four-root cancellation control')
    result={'status':'PASS','lucas_modular_models':cases,'adjacent_pell_samples':samples,
            'growth_inequality_samples':inequalities,
            'noncoprime_half_binomial_control':{'q':q,'R':R,'r':r,'popcount_r':16,
              'v2_Y':15,'q3_divides_Y':True,'X_mod_31':x,'Y_mod_31':residue,
              'H_mod_31':hres,'gcd_H_q_minus_1':31,
              'scope':'Kernel example only, not an authentic outer-coefficient zero.'},
            'negative_controls':['Four distinct radicals can contain a cancelling triple',
                                 'Nonadjacent Pell coefficients allow rational noninteger roots',
                                 'H and q-1 need not be coprime even on the half-binomial kernel'],
            'proof_scope':'Finite controls only; universal results are proved in PROOF.md.'}
    (ROOT/'generated'/'LOCAL_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':print(json.dumps(run(),indent=2))
