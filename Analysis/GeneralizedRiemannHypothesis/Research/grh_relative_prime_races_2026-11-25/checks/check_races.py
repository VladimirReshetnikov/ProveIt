#!/usr/bin/env python3
"""Exact combinatorics and finite Frobenius factorization; floating logs only for diagnostics."""
import csv
import itertools as it
import math
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]

def cycle_type(g):
    seen=set(); lengths=[]
    for i in range(len(g)):
        if i not in seen:
            j=i; l=0
            while j not in seen:
                seen.add(j); l+=1; j=g[j]
            lengths.append(l)
    return tuple(sorted(lengths))

def tower_weights(sizes):
    assert sizes[-1]==1 and all(a>b and a%b==0 for a,b in zip(sizes,sizes[1:]))
    ns=[a//b for a,b in zip(sizes,sizes[1:])]
    cs=[1]
    for j in range(1,len(ns)):
        cs.append(sum(c*(n-1) for c,n in zip(cs,ns)))
    # Test all possible subgroup membership strata, including identity.
    for layer in range(1,len(sizes)+1):
        vals=[n*int(layer>i)-int(layer>i-1) for i,n in enumerate(ns,1)]
        expected= -1 if layer==1 else (sizes[0]-sizes[1] if layer==len(sizes) else 0)
        assert sum(c*v for c,v in zip(cs,vals))==expected, (sizes,layer,vals,cs)
    return ns,cs

def group_check():
    ct=Counter(cycle_type(g) for g in it.permutations(range(4)))
    assert ct=={(1,1,1,1):1,(1,1,2):6,(2,2):3,(1,3):8,(4,):6}
    ns,cs=tower_weights([12,4,1]); assert (ns,cs)==([3,4],[1,2])
    for sizes in ([6,3,1],[24,12,4,1],[60,1],[128,64,16,2,1],[12,6,3,1]):
        tower_weights(sizes)
    # Check a variety of chains, in abstract membership strata.
    for length in range(1,6):
        for factors in it.product(range(2,6),repeat=length):
            sizes=[math.prod(factors[i:]) for i in range(length+1)]
            tower_weights(sizes)
    weights={}
    for typ,n in sorted(ct.items()):
        is_a4=(4-len(typ))%2==0
        is_v4=typ in ((1,1,1,1),(2,2))
        is_e=typ==(1,1,1,1)
        w1=3*is_v4-is_a4; w2=4*is_e-is_v4; w=w1+2*w2
        assert w==8*is_e-int(typ==(1,3))
        weights[typ]=w
        print('S4',typ,n,w1,w2,w)
    assert sum(ct[t]*w for t,w in weights.items())==0
    assert sum(ct[t] for t,w in weights.items() if w)==9
    # Inclusion-exclusion coefficient for direct products: indicator of restrictions.
    for m in range(2,6):
        ns=tuple(range(2,2+m))
        for split in it.product((0,1),repeat=m):
            lhs=math.prod(n*b-1 for n,b in zip(ns,split))
            rhs=sum((-1)**(m-sum(mask))*math.prod(n*b for n,b,a in zip(ns,split,mask) if a)
                    for mask in it.product((0,1),repeat=m))
            assert lhs==rhs
    print('All exact group, normal-chain and mixed-product checks passed.')
    return weights

def trim(a):
    a=list(a)
    while a and a[-1]==0: a.pop()
    return a

def rem(a,b,p):
    a=trim(a); b=trim(b); assert b
    inv=pow(b[-1],-1,p)
    while len(a)>=len(b):
        q=a[-1]*inv%p; k=len(a)-len(b)
        for i,c in enumerate(b): a[i+k]=(a[i+k]-q*c)%p
        a=trim(a)
    return a

def gcd(a,b,p):
    while b: a,b=b,rem(a,b,p)
    return a

def mul(a,b,p):
    c=[0]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    # x^4 = x+1 modulo x^4-x-1
    for i in range(6,3,-1):
        c[i-4]=(c[i-4]+c[i])%p; c[i-3]=(c[i-3]+c[i])%p
    return c[:4]

def power(a,n,p):
    result=[1,0,0,0]
    while n:
        if n&1: result=mul(result,a,p)
        n//=2
        if n: a=mul(a,a,p)
    return result

def factor_type(p):
    assert p!=283
    f=[p-1,p-1,0,0,1]; X=[0,1,0,0]
    xp=power(X,p,p)
    roots=len(gcd(f,trim([(a-b)%p for a,b in zip(xp,X)]),p))-1
    if roots==4: return (1,1,1,1)
    if roots==2: return (1,1,2)
    if roots==1: return (1,3)
    assert roots==0, (p,roots)
    xpp=power(xp,p,p)
    deg=len(gcd(f,trim([(a-b)%p for a,b in zip(xpp,X)]),p))-1
    assert deg in (0,4), (p,deg)
    return (2,2) if deg==4 else (4,)

def primes(n):
    a=bytearray(b'\x01')*(n+1); a[:2]=b'\x00\x00'
    for i in range(2,math.isqrt(n)+1):
        if a[i]: a[i*i:n+1:i]=b'\x00'*((n-i*i)//i+1)
    return (i for i in range(2,n+1) if a[i])

def main():
    weights=group_check()
    assert 256*(-1)**3-27*(-1)**4==-283
    assert factor_type(2)==(4,)
    witness=next(p for p in primes(100) if p!=283 and factor_type(p)==(1,3))
    print('Galois witnesses: p=2 (4-cycle), p=%d (3-cycle).'%witness)
    xs=[10,20,40,80,160,320]
    bounds=sorted(set(xs+[x*x for x in xs])); sums={}; counts=Counter(); logs=[]; logs_over_p=[]
    ps=iter(primes(bounds[-1])); p=next(ps,None)
    for bound in bounds:
        while p is not None and p<=bound:
            if p!=283:
                typ=factor_type(p); counts[typ]+=1
                if p<=101:
                    assert typ.count(1)==sum((x**4-x-1)%p==0 for x in range(p))
                w=weights[typ]
                if w:
                    logs.append(w*math.log(p)); logs_over_p.append(w*math.log(p)/p)
            p=next(ps,None)
        sums[bound]=(math.fsum(logs_over_p)-math.fsum(logs)/bound,counts.copy())
    with (ROOT/'checks'/'quartic_race.csv').open('w',newline='') as fp:
        wr=csv.writer(fp);wr.writerow(['x','P_x','P_x_squared','difference','sqrt_x_times_difference','split_count_x2','one_three_count_x2'])
        for x in xs:
            a=sums[x][0]; b,c=sums[x*x]; diff=a-b
            wr.writerow([x,format(a,'.12g'),format(b,'.12g'),format(diff,'.12g'),format(math.sqrt(x)*diff,'.12g'),c[(1,1,1,1)],c[(1,3)]])
    print('Exact factorization counts through',bounds[-1],dict(sorted(counts.items())))
    print('quartic_race.csv: finite diagnostics only; logarithms use floating point.')

if __name__=='__main__': main()
