"""Exact rank rule, witness reconstruction, and independent Newton replay."""
from itertools import combinations_with_replacement, groupby
from collections import Counter
from fractions import Fraction as F
from math import comb,lcm
from random import Random

def candidates(p,t):
    return sorted({i+p*j for i in range(t-1) for j in range(t-1-i)}|{t-1})

def vec(p,res,k):
    return [comb(k,i)*pow(x,k-i,p)%p if k>=i else 0
            for x,m in Counter(res).items() for i in range(m)]

def reduce_row(b,v,p):
    v=list(v)
    for i in range(len(v)):
        if v[i] and i in b:
            x=v[i]; v=[(a-x*y)%p for a,y in zip(v,b[i])]
    return v

def insert(b,v,p):
    v=reduce_row(b,v,p)
    if any(v):
        i=next(i for i,x in enumerate(v) if x)
        u=pow(v[i],-1,p); b[i]=[x*u%p for x in v]

def profile(p,t,r):
    w=lambda k:r*k-k//p
    return [(a,list(g)) for a,g in groupby(sorted((k for k in candidates(p,t) if w(k)<=w(t-1)),key=w),w)]

def count(p,res,r,vs=None,groups=None):
    t=len(res)
    if vs is None: vs={k:vec(p,res,k) for k in candidates(p,t)}
    if groups is None: groups=profile(p,t,r)
    best=t-1; lower=[]; b={}
    for _,ks in groups:
        for k in ks:
            if k>best and any(reduce_row(b,vs[k],p)):
                best=k; lower=b.copy()
        for k in ks:insert(b,vs[k],p)
    return best,lower

def poly_times(v,n):
    a=[0]*(len(v)+1)
    for i,x in enumerate(v):
        a[i]-=n*x; a[i+1]+=x
    return a

def witness(p,ns,r):
    k,b=count(p,[n%p for n in ns],r)
    t=len(ns)
    if k==t-1:
        coeff=[F(1,prod(n-m for m in ns if m!=n)) for n in ns]
    else:
        # Build a functional on jets annihilating lower span.
        a=reduce_row(b,vec(p,[n%p for n in ns],k),p)
        j=next(i for i,x in enumerate(a) if x)
        # RREF not required: apply the reduction map before extracting j.
        functional=lambda v:reduce_row(b,v,p)[j]*pow(a[j],-1,p)%p
        w=lambda j:r*j-j//p
        values=[0 if w(i)<w(k) else functional(vec(p,[n%p for n in ns],i)) for i in range(t)]
        coeff=[]
        for n in ns:
            v=[1]; denom=1
            for m in ns:
                if m!=n: v=poly_times(v,m); denom*=n-m
            coeff.append(F(sum(x*y for x,y in zip(v,values)),denom))
    d=lcm(*(c.denominator for c in coeff))
    return k,[int(d*c) for c in coeff]

def prod(it):
    x=1
    for y in it:x*=y
    return x

def valuation(p,x):
    if not x:return float('inf')
    n=0
    while x%p==0:x//=p;n+=1
    return n

def newton(p,ns,cs,r):
    w=[(valuation(p,sum(c*comb(n,k) for n,c in zip(ns,cs) if k<=n))+r*k,-k)
       for k in range(max(ns)+1)]
    return -min(w)[1]

def points(p,t):
    ks=candidates(p,t)
    base=F(1,p-1)
    return [base]+sorted({F(b//p-a//p,b-a) for a in ks for b in ks if a<b and
                          F(b//p-a//p,b-a)>base})

def verify():
    rng=Random(71621); ntest=0
    for p in [3,5,7,11,13,17,19]:
        for t in range(2,p+1):
            for _ in range(18):
                ns=sorted(rng.sample(range(3*p+1),t))
                for r in [F(1,p-1)+F(1,p*p),F(1,p-2),F(2,2*p-3),
                          F(1,max(1,p-t+1)),F(1),F(3,2)]:
                    if r<=F(1,p-1): continue
                    k,cs=witness(p,ns,r)
                    assert newton(p,ns,cs,r)==k,(p,t,ns,r,k,cs)
                    ntest+=1
    for ns,cs,k in [
        ([0,1,2,7,8,14],[-17792,50400,-36946,14976,-10465,170],14),
        ([0,1,3,7,8,14],[86,504,-343,255,-161,2],8)]:
        assert count(7,[n%7 for n in ns],F(1,5))[0]==k
        assert newton(7,ns,cs,F(1,5))==k
    for ns, want in [([0,1,2,7,8,14],[(F(1,5),14,7),(F(1,2),7,5)]),
                     ([0,1,3,7,8,14],[(F(2,11),14,8),(F(1,4),8,7),(F(1,2),7,5)])]:
        rs=points(7,6)
        res=[x%7 for x in ns]
        ans=[count(7,res,(a+b)/2)[0] for a,b in zip(rs,rs[1:])]+[count(7,res,rs[-1]+1)[0]]
        got=[(r,ans[i-1],ans[i]) for i,r in enumerate(rs) if i and ans[i]!=ans[i-1]]
        assert got==want and all(count(7,res,r)[0]==old for r,old,new in got)
    print(ntest,'rank-to-rational-witness checks by exact binomial expansion.')

def universal_7():
    p=t=7
    # Affine residue changes preserve lower-weight spans: binomial
    # expansion of (aT+b)^i(aU+b)^j uses no higher digit sum and
    # strictly decreases weight except at the top term.
    ks=candidates(p,t)
    rs=points(p,t)
    sample=[(a+b)/2 for a,b in zip(rs,rs[1:])]+[rs[-1]+1]
    groups=[profile(p,t,r) for r in sample]
    best=[0]*len(sample); examples=[None]*len(sample)
    seen=set()
    for res in combinations_with_replacement(range(p),t):
        if res in seen:continue
        seen.update(tuple(sorted((a*x+b)%p for x in res)) for a in range(1,p) for b in range(p))
        vs={k:vec(p,res,k) for k in ks}
        for j,r in enumerate(sample):
            k,_=count(p,res,r,vs,groups[j])
            if k>best[j]:best[j]=k;examples[j]=res
    # Confirm the larger count is retained at all actual transition endpoints.
    for j in range(1,len(rs)):
        if best[j]==best[j-1]:continue
        r=rs[j]; eg=examples[j-1]
        assert count(p,eg,r)[0]==best[j-1]
        ns=[]
        for x,m in Counter(eg).items():
            ns.extend(x+p*i for i in range(m))
        ns.sort()
        k,cs=witness(7,ns,r)
        assert k==best[j-1] and newton(7,ns,cs,r)==k
        print('p=t=7:',best[j-1],'through',r,'then',best[j],'; endpoint support',ns)
    print(len(seen),'residue multisets represented.')
    return rs,best,examples

if __name__=='__main__':
    verify()
    universal_7()
