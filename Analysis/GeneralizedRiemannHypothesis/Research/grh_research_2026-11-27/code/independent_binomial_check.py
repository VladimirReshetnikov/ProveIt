#!/usr/bin/env python3
"""Independent exhaustive binomial-minor comparisons; fixed seed, standard library."""
import sys,math,itertools,json,random
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from sparse_disk import solve, newton_count

def det(M):
    M=[[Fraction(x) for x in row] for row in M]
    out=Fraction(1)
    for j in range(len(M)):
        h=next((k for k in range(j,len(M)) if M[k][j]),None)
        if h is None:return 0
        if h!=j:M[h],M[j]=M[j],M[h];out=-out
        a=M[j][j];out*=a
        for k in range(j+1,len(M)):
            q=M[k][j]/a
            for l in range(j+1,len(M)):M[k][l]-=q*M[j][l]
    return out

def val(x,p):
    x=Fraction(x);a=abs(x.numerator);b=x.denominator;v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    return v

def direct(E,p,r):
    E=[e-min(E) for e in E];t=len(E);best=None;u=set();nb=0
    for J in itertools.combinations(range(max(E)+1),t):
        a=det([[math.comb(e,k) if e>=k else 0 for k in J] for e in E])
        if not a:continue
        if r=='open':w=(Fraction(val(a,p))+Fraction(sum(J),p-1),sum(J))
        else:w=(Fraction(val(a,p))+Fraction(r)*sum(J),0)
        if best is None or w<best:best=w;u=set(J);nb=1
        elif w==best:u.update(J);nb+=1
    return max(u),nb
random.seed(221)
rows=[]
for p,t,maxE in [(2,2,10),(2,3,10),(2,4,10),(3,3,10),(3,4,10),(3,5,10),(5,4,10)]:
    for r in ['open',str(Fraction(1,2*p)),str(Fraction(1,p+1)),str(Fraction(1,p-1)),str(Fraction(1,p-1)+Fraction(1,10)),str(Fraction(1,p-1)+Fraction(1,2)),str(Fraction(1,p-1)+1)]:
        for rep in range(5):
            E=sorted(random.sample(range(maxE+1),t))
            a=solve(E,p,r);b,nb=direct(E,p,r)
            if newton_count(E,a['witness_coefficients'],p,r)!=b:raise AssertionError(('witness',E,p,r,a,b))
            if r=='open' or Fraction(r)>Fraction(1,p-1):
                binomial=solve(E,p,r,method='binomial')
                if binomial['maximum']!=a['maximum']:raise AssertionError(('method',E,p,r,a,binomial))
            if a['maximum']!=b: raise AssertionError((E,p,r,a,b))
            rows.append(dict(E=E,p=p,r=r,maximum=b,min_bases=nb))
print(json.dumps(dict(cases=len(rows),all_match=True,checks=rows),indent=2))
