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
    total=0
    for p in (7,11,13,17):
        e = (p,p+1,2*p,p+2,2*p+1,3*p,p+3,2*p+2,3*p+1,4*p)
        for roots in combinations_with_replacement(range(p),6):
            profile=sorted(Counter(roots).values())
            jets=[(x,i) for x,m in Counter(roots).items() for i in range(m)]
            rows={k:[comb(k,i)*pow(x,k-i,p)%p if k>=i else 0 for x,i in jets]
                  for k in (*range(6),*e)}
            def test(base, targets):
                B={}
                for k in base: insert(B,rows[k],p)
                for k in targets: assert not insert(B,rows[k],p),(p,roots,k)
            if profile!=[1,2,3]:
                test([0,1,2,p,p+1],[2*p])
                test([0,1,2,3,p,p+1],[p+2,2*p+1,3*p])
                test([0,1,2,3,4,p,p+1],[p+3,2*p+2,3*p+1,4*p])
            else:
                test([0,1,2,p,p+1,2*p],[2*p+1,3*p,p+3,2*p+2,3*p+1,4*p])
                test([0,1,2,3,4,p,p+1],[p+2,2*p])
            total+=1
    print(total,'six-slot residue multisets checked.')

def coeffs(nodes, rows, target):
    # Solve the six exact moment equations.
    a=[[Q(n**k) for n in nodes]+[Q(y)] for k,y in zip(rows,target)]
    for col in range(6):
        idx=next(i for i in range(col,6) if a[i][col])
        a[col],a[idx]=a[idx],a[col]
        d=a[col][col]
        a[col]=[x/d for x in a[col]]
        for i in range(6):
            if i!=col:
                d=a[i][col]
                a[i]=[x-d*y for x,y in zip(a[i],a[col])]
    return [row[-1] for row in a]

def vp(n,p):
    if not n:return float('inf')
    i=0
    while n%p==0:
        i+=1;n//=p
    return i

def val(n,p): return vp(n.numerator,p)-vp(n.denominator,p)

def factorial_val(k,p):
    s=0
    while k:
        k//=p;s+=k
    return s

def witness_checks():
    checks=0
    for p in primes(53):
        if p<7:continue
        c=(-2*pow(3,-1,p))%p
        for ns,row,depth,indices in [
            ([0,p,2*p,1,p+1,2],[0,1,2,p,p+1,2*p],Q(1,p-2),[4,p+2,2*p]),
            ([0,p,2*p,1,2,c],list(range(6)),Q(1,p-4),[5,p+1])]:
            cs=coeffs(ns,row,[0,0,0,0,0,1])
            assert all(cs)
            if p==7: print('p=7 witness',ns,cs)
            vals=[]
            for k in range(6*p+1):
                m=sum((a*n**k for a,n in zip(cs,ns)),Q(0))
                vals.append(val(m,p)+k*depth-factorial_val(k,p))
            assert [k for k,v in enumerate(vals) if v==min(vals)]==indices
            checks+=len(vals)
    print(checks,'rational witness moments checked.')

if __name__=='__main__':
    span_checks()
    witness_checks()
