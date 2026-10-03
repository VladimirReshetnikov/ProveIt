#!/usr/bin/env python3
"""Exact lower approximants to the frontend's noncomputable natural density.
No error bar, convergence modulus or randomness claim is attached to them.
"""
from pathlib import Path
from fractions import Fraction
import json
R=Path(__file__).resolve().parent
T=json.loads((R/'tm_table.json').read_text())

def halts(L,RR,t):
    q='A';s=0
    for j in range(t+1):
        row=T[q+str(s)]
        if row is None:return True
        if j==t:return False
        w,d,q=row
        if d=='R':RR,s=divmod(RR,2);L=2*L+w
        else:L,s=divmod(L,2);RR=2*RR+w

def valuation(a,p):
    n=0
    while a%p==0:a//=p;n+=1
    return n

checks=0
for N in (1,7,100,10001):
    counts={}
    for a in range(1,N+1):
        pair=valuation(a,2),valuation(a,3);counts[pair]=counts.get(pair,0)+1
    for L in range(8):
        for RR in range(8):
            k=2**L*3**RR
            expected=N//k-N//(2*k)-N//(3*k)+N//(6*k)
            assert counts.get((L,RR),0)==expected;checks+=1
# Exact geometric finite-box mass and omitted-weight formula.
for K in range(9):
    for J in range(9):
        mass=sum((Fraction(1,3*2**L*3**RR) for L in range(K+1) for RR in range(J+1)),Fraction())
        a=Fraction(1,2**(K+1));b=Fraction(1,3**(J+1))
        assert mass==(1-a)*(1-b) and 1-mass<=a+b
        checks+=1
approximants=[];prev=Fraction();remainder_checks=0
for t in (0,1,2,4,8,16,32,64,128):
    accepted=[(L,RR) for L in range(t+1) for RR in range(t+1) if halts(L,RR,t)]
    value=sum((Fraction(1,3*2**L*3**RR) for L,RR in accepted),Fraction())
    assert prev<=value<1;prev=value
    # The uniform counting bound applies to every set of valuation pairs.
    # Test it here for these decidable finite subsets, not the uncomputable full set.
    for N in (1,7,100,10001,10**80):
        count=0
        for L,RR in accepted:
            k=2**L*3**RR
            count+=N//k-N//(2*k)-N//(3*k)+N//(6*k)
        K=N.bit_length()-1;J=0;power=3
        while power<=N:J+=1;power*=3
        assert abs(Fraction(count)-N*value)<=4*(K+1)*(J+1)+2
        remainder_checks+=1
    approximants.append({'t':t,'confirmed_pairs':len(accepted),'numerator':value.numerator,'denominator':value.denominator,
                         'decimal_lower_bound_18dp':f'{(value.numerator*10**18//value.denominator)//10**18}.{(value.numerator*10**18//value.denominator)%10**18:018d}'})
assert halts(6,0,7) and not halts(6,0,6)
out={'status':'passed','finite_cylinder_and_tail_checks':checks,'finite_subset_counting_remainder_checks':remainder_checks,'approximants':approximants,
     'interpretation':'Exact computable lower bounds δ_t only. The limit is noncomputable; no effective error guarantee is supplied. Proof is in PROOF.md §9.'}
(R/'density_lower_bounds.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
