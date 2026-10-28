#!/usr/bin/env python3
"""Exact scoped checks: one-leading-digit Hermite loss and separator witness.
These are limitations of particular representations, not SAT lower bounds.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse,json


def need(condition,message):
    if not condition:
        raise RuntimeError(message)


def valuation(n,p):
    need(n!=0,'Zero has no finite valuation')
    n=abs(n);v=0
    while n%p==0:n//=p;v+=1
    return v


def first_digit(n,p):
    v=valuation(n,p)
    return (n//(p**v))%p


def hermite_checks():
    cases=0;total=Fraction(0)
    for p in [2,3,5,7]:
        for a in range(1,5):
            if p**(a+1)>4000:continue
            for u in range(1,a+1):
                for i in range(u):
                    t=p**i;D=p**(a-i);H=u-i
                    direct=sum((u-valuation(q,p))*(valuation(q,p)-valuation(t-q,p))
                               for q in range(1,p**(a+1)) if q!=t and first_digit(q,p)==1 and valuation(q,p)<u)
                    formula=D*sum(Fraction(j,p**j)*(max(H-j,0)-(p-1)*H)for j in range(1,a-i+1))
                    need(direct==formula,'One-digit Hermite identity failed')
                    need(formula<=0,'Unexpected sign')
                    cases+=1;total+=formula
    return {'cases':cases,'sum_of_losses':str(total),'status':'PASS'}


def locality_checks():
    counts={}
    for p in [2,3,5,7]:
        nontrivial=0
        for B in product([0,1],repeat=p):
            # A is determined by shift one; compare every other nonzero shift.
            A=tuple(B[(x+1)%p]for x in range(p))
            if all(A[x]==B[(x+c)%p]for x in range(p)for c in range(1,p)):
                nontrivial+=int(len(set(B))>1)
        need(nontrivial==(2 if p==2 else 0),'Digit-locality claim failed')
        counts[str(p)]=nontrivial
    return {'nonconstant_binary_labelings':counts,'status':'PASS'}


def separator_checks():
    limit=32
    P=[Fraction(0)]*(limit+1);S=P.copy();rows=[]
    for n in range(2,limit+1):
        pc=[Fraction(4,3)*a*(n-a)+max(P[a],P[n-a])for a in range(1,n)]
        sc=[Fraction(2,3)*(n-a)*(2*a+1)+max(S[a],P[n-a])for a in range(1,n)]
        P[n]=min(pc);S[n]=min(sc)
        rows.append({'n':n,'ordinary':str(P[n]),'star':str(S[n]),
                     'optimal_star_side_sizes':[a for a in range(1,n)if sc[a-1]==S[n]]})
    for n in [4,8,16,32]:
        need(S[n]==Fraction((n-1)*(4*n+10),9),'Unbalanced witness differs at target arity')
    need(S[15]<Fraction((15-1)*(4*15+10),9),'Counterexample to all-n formula was lost')
    return {'status':'PASS','rows':rows,'certified_arities':[4,8,16,32],
            'scope':'All binary separator trees on these finite arities under the specified entropy witness.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    result={'status':'PASS','hermite':hermite_checks(),'locality':locality_checks(),'unbalanced':separator_checks()}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
