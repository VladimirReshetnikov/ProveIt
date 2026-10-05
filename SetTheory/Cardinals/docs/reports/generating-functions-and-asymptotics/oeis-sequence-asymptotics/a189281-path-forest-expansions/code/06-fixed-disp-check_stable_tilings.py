"""Exact independent chain DP versus the stable polynomial, and brute-force IE."""
from collections import defaultdict
from fractions import Fraction
from itertools import product, permutations
from math import factorial, prod
from pathlib import Path
import hashlib,json

def ff(n,k):
    return prod(range(n-k+1,n+1))
def rf(n,k):
    return prod(range(n,n+k))

def mul(A,B,J):
    out=defaultdict(int)
    for a,v in A.items():
        for b,w in B.items():
            c=tuple(x+y for x,y in zip(a,b))
            if sum((i+1)*x for i,x in enumerate(c))<=J:
                out[c]+=v*w
    return dict(out)

def chain(N,J):
    zero=(0,)*J
    dp=[{zero:1}]
    for n in range(1,N+1):
        cur=defaultdict(int,dp[n-1])
        for size in range(2,min(n,J+1)+1):
            for a,v in dp[n-size].items():
                b=list(a);b[size-2]+=1;b=tuple(b)
                if sum((i+1)*x for i,x in enumerate(b))<=J: cur[b]+=v
        dp.append(dict(cur))
    return dp[N]

def chains(lengths,J):
    out={(0,)*J:1}
    for N in lengths: out=mul(out,chain(N,J),J)
    return out

def stable(n,r,a):
    c=sum(a);j=sum((i+1)*x for i,x in enumerate(a))
    ans=Fraction(0)
    for b in product(*(range(x+1) for x in a)):
        h=sum(b)
        ans+=Fraction((-1)**h*rf(r-1,h)*ff(n-j-h,c-h)*
                      prod((i+1)**x for i,x in enumerate(b)),
                      prod(factorial(x)*factorial(y-x) for x,y in zip(b,a)))
    if ans.denominator!=1: raise ValueError("Nonintegral stable coefficient")
    return int(ans)

def exact_count(n,r,s):
    J=max(n-1,0)
    if J==0:return factorial(n)
    cr=chains([len(range(i,n,r)) for i in range(min(r,n))],J)
    cs=chains([len(range(i,n,s)) for i in range(min(s,n))],J)
    total=0
    for a,v in cr.items():
        c=sum(a);j=sum((i+1)*x for i,x in enumerate(a))
        total+=(-1)**j*v*cs.get(a,0)*factorial(n-j-c)*prod(factorial(x) for x in a)
    return total

records=[];nchecks=0
for lengths in [(12,12),(12,15),(13,14),(12,12,12),(12,13,17),(12,12,12,12)]:
    J=6;cr=chains(lengths,J)
    for a,v in cr.items():
        expected=stable(sum(lengths),len(lengths),a)
        if expected!=v:raise ValueError((lengths,a,v,expected))
        nchecks+=1
    records.append({"lengths":lengths,"profiles":len(cr)})
brute=[]
for n in range(1,9):
    for r,s in [(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)]:
        actual=sum(all(p[i+r]-p[i]!=s for i in range(n-r))
                   for p in permutations(range(1,n+1)))
        via=exact_count(n,r,s)
        if actual!=via:raise ValueError((n,r,s,actual,via))
        brute.append([n,r,s,actual])
expected22=[1,1,2,5,18,75,410,2729,20906,181499,1763490,18943701,222822578]
for n,expected in enumerate(expected22):
    actual=exact_count(n,2,2)
    if actual!=expected:raise ValueError((n,actual,expected))
result={"passed":True,"stable_profile_equalities":nchecks,"stable_cases":records,
        "independent_permutation_checks":brute,"OEIS_A189281_terms_checked":len(expected22)}
out=Path(__file__).with_suffix(".json")
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"passed":True,"stable_profile_equalities":nchecks,
                  "brute_force_checks":len(brute),"OEIS_terms":len(expected22)}))
