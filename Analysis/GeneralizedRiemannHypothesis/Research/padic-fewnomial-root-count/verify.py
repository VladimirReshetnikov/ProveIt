"""Independent exact residue-jet and rational Newton-profile checks."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import comb,isqrt

def primes(n):
    return [k for k in range(2,n+1) if all(k%i for i in range(2,isqrt(k)+1))]

def insert(B,v,p):
    v=list(v)
    for i in range(len(v)):
        x=v[i]
        if not x: continue
        if i in B:
            row=B[i]
            v=[(a-x*b)%p for a,b in zip(v,row)]
        else:
            inv=pow(x,-1,p)
            B[i]=[(a*inv)%p for a in v]
            return True
    return False

def span_checks():
    c=s=0
    for p in primes(17):
        for t in (4,5):
            if t>p: continue
            for roots in combinations_with_replacement(range(p),t):
                jets=[(x,i) for x,m in Counter(roots).items() for i in range(m)]
                def data(k):
                    return [comb(k,i)*pow(x,k-i,p)%p if k>=i else 0 for x,i in jets]
                if t==4:
                    targets=[([0,1,2,p],[p+1,2*p])]
                else:
                    targets=[([0,1,2,p,p+1],[2*p]),
                             ([0,1,2,3,p,p+1],[p+2,2*p+1,3*p])]
                for basis,exps in targets:
                    B={}
                    for k in basis: insert(B,data(k),p)
                    for k in exps:
                        assert not insert(B,data(k),p),(p,roots,k)
                        s+=1
                c+=1
    print(c,'residue multisets;',s,'exact span comparisons.')

def vp(a,p):
    if not a: return None
    v=0
    while a%p==0:
        a//=p
        v+=1
    return v

def shift(poly):
    return [sum(a*comb(i,j) for i,a in poly.items() if i>=j) for j in range(max(poly)+1)]

def min_indices(poly,p,r):
    data=[(vp(a,p)+r*k,k) for k,a in enumerate(poly) if a]
    m=min(x for x,k in data)
    return m,[k for x,k in data if x==m]

def profile_checks():
    checks=0
    for p in primes(97):
        for t in (3,4,5):
            if t>p: continue
            poly=[p**(2*t-1)]+[0]*(t-2)+[comb(p,k) for k in range(t-1,p+1)]
            assert min_indices(poly,p,Q(2))==(2*t-1,[0,t-1])
            assert min_indices(poly,p,Q(1,p-t+1))[1]==[t-1,p]
            checks+=2
        if p<5: continue
        poly=shift({0:1,p-1:-p*p,p:2*(p*p-1)+p**5,p+1:-p*p,2*p:1})
        assert min_indices(poly,p,Q(3,4))==(5,[0,4])
        assert min_indices(poly,p,Q(1,p-3))[1]==[4,p+1]
        checks+=2
    print(checks,'exact Newton-profile checks.')
    k=2*5**12 # a large factorial-only admissible index, by its base-5 digit sum
    assert Q(k,10**9)+Q(2,4)<=4*(Q(1,4)+Q(1,10**9))
    print('At p=5 and r=1/4+10^-9 the factorial-only index permits',k)

if __name__=='__main__':
    span_checks()
    profile_checks()
