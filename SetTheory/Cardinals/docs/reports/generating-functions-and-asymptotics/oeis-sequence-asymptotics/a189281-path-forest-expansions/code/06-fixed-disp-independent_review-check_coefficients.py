"""Independent rational finite-difference reconstruction of fixed-displacement asymptotics.
Uses only the standard library. No producer code or Touchard-polynomial routine is imported.
"""
from fractions import Fraction as F
from math import factorial
from itertools import combinations
from collections import Counter
from pathlib import Path
import json

def mul(a,b,M):
    c=[0]*(M+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=M:c[i+j]+=x*y
    return c

def profiles(D,lo=1):
    if D==0:yield ();return
    for d in range(lo,D+1):
        for p in profiles(D-d,d):yield (d,)+p

def falling_norm(A,B,M):
    p=[1]+[0]*M
    for v in range(A,A+B):p=mul(p,[1,-v],M)
    return p

def chain_normalized(r,k,higher,M):
    # n^(-c) prod(alpha_i!) C_r(n;alpha), expanded in u=1/n.
    c=k+len(higher);D=sum(higher);j=c+D
    e=[1]+[0]*M
    for w in [1]*k+[d+1 for d in higher]:e=mul(e,[1,w],M)
    ans=[0]*(M+1);rising=1
    for h in range(min(M,c)+1):
        if h:rising*=r+h-2
        f=falling_norm(j+h,c-h,M-h)
        coeff=(-1)**h*rising*e[h]
        for u,v in enumerate(f):ans[u+h]+=coeff*v
    return ans

def profile_poly(r,s,k,higher,M):
    c=k+len(higher);j=c+sum(higher)
    result=mul(chain_normalized(r,k,higher,M),chain_normalized(s,k,higher,M),M)
    # Invert the falling denominator by a separate complete-homogeneous recurrence.
    for v in range(j+c):
        out=[0]*(M+1)
        for ell in range(M+1):out[ell]=result[ell]+(v*out[ell-1] if ell else 0)
        result=out
    return result

def poisson_alternating(values,degree):
    # For a degree-d polynomial P, e sum(-1)^k P(k)/k!
    # is sum_j (-1)^j Delta^j P(0)/j!.
    diffs=list(values);answer=F(0)
    for j in range(degree+1):
        answer+=F((-1)**j*diffs[0],factorial(j))
        diffs=[b-a for a,b in zip(diffs,diffs[1:])]
    if any(diffs):raise RuntimeError(('polynomial degree',degree,diffs))
    return answer

def reconstruct(r,s,K):
    ans=[F(0)]*(K+1);checks=0;profile_count=0
    for D in range(K+1):
        for higher in profiles(D):
            M=K-D;degree=2*M
            polys=[profile_poly(r,s,k,higher,M) for k in range(degree+3)]
            alpha=Counter(higher);den=1
            for multiplicity in alpha.values():den*=factorial(multiplicity)
            sign=(-1)**(len(higher)+D)
            for ell in range(M+1):
                # Tighter degree applies individually at each retained order.
                vals=[p[ell] for p in polys]
                ans[D+ell]+=F(sign,den)*poisson_alternating(vals,2*ell)
                checks+=1
            profile_count+=1
    return ans,checks,profile_count

main,checks,profile_count=reconstruct(2,2,6)
expected=[1,3,2,1,0,3,26]
if main!=expected:raise RuntimeError(('a22',main))
general=0
for r in range(1,5):
    for s in range(1,5):
        ans,cc,pp=reconstruct(r,s,3)
        wanted=[F(1),F(r+s-1),F(r*r-r+s*s-s,2),F((r+s-1)*(r*r-4*r*s+4*r+s*s+4*s-6),6)]
        if ans!=wanted:raise RuntimeError(('general',r,s,ans,wanted))
        general+=1;checks+=cc
# Fresh enumeration of selected edges in two arithmetic-progression chains.
stable_checks=0
for n in (4,8,12,16):
    edges=list(range(1,n-1))
    for j in range(min(4,n//4)+1):
        counted=Counter()
        for selected in combinations(edges,j):
            chosen=set(selected);runs=[]
            for start in selected:
                if start-2 in chosen:continue
                length=1
                while start+2*length in chosen:length+=1
                runs.append(length+1)
            counted[tuple(sorted(runs))]+=1
        for sizes,value in counted.items():
            k=sizes.count(2);higher=tuple(i-2 for i in sizes if i>=3);c=len(sizes)
            p=chain_normalized(2,k,higher,c)
            numerator=sum(F(v,n**ell) for ell,v in enumerate(p))*n**c
            denom=1
            for multiplicity in Counter(sizes).values():denom*=factorial(multiplicity)
            if numerator/denom!=value:raise RuntimeError(('stable count',n,j,sizes,value,numerator/denom))
            stable_checks+=1
result={'status':'PASS','a22_order':6,'a22_coefficients':[str(v) for v in main],'higher_defect_profiles':profile_count,'finite_difference_polynomial_checks':checks,'general_r_s_pairs_through_order3':general,'direct_two_chain_profile_counts':stable_checks,'method':'Standard-library truncated products and Newton forward differences; fresh edge-subset enumeration; no imported producer code.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
