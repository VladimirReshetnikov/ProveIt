#!/usr/bin/env python3
"""Exact finite analogues of the orbital projection and complementary completion.

These are regression tests, NOT a proof over local fields or a Lean build.
Python standard library only.
"""
from fractions import Fraction as Q
from itertools import product

p = 3
I = (1,0,0,1)

def det(A, m=p):
    a,b,c,d=A
    return (a*d-b*c)%m

def mul(A,B,m=p):
    a,b,c,d=A; e,f,g,h=B
    return ((a*e+b*g)%m,(a*f+b*h)%m,(c*e+d*g)%m,(c*f+d*h)%m)

def inv(A,m=p):
    a,b,c,d=A
    t=pow(det(A,m),-1,m)
    return tuple(t*x%m for x in (d,-b,-c,a))

G=tuple(g for g in product(range(p), repeat=4) if det(g))
K=tuple(g for g in G if g[2]==0) # upper triangular, nonnormal
assert len(G)==48 and len(K)==12
assert any(mul(mul(g,k),inv(g)) not in K for g in G for k in K)
chi=lambda g: 1 if det(g)==1 else -1
X=tuple((orbit,g) for orbit in range(2) for g in G)
U={(o,g) for o in range(2) for g in K}

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def total(vs):
    s=(Q(0),)*len(X)
    for v in vs: s=add(s,v)
    return s
index={x:i for i,x in enumerate(X)}
def rho(h,f):
    return tuple(chi(h)*f[index[o,mul(y,h)]] for o,y in X)
def J(f):
    return tuple(sum(chi(g)*f[index[o,mul(y,g)]] for g in G)/Q(len(K)) for o,y in X)
def P(f):
    return tuple(a if x in U else Q(0) for x,a in zip(X,J(f)))

def left_cosets():
    left=set(G); result=[]
    while left:
        r=min(left); coset={mul(k,r) for k in K}
        result.append((r,coset)); left-=coset
    return result

def certificate(f):
    """Equation (finite): choose H={1}, legitimate for any finite-group datum."""
    parts=[]
    for s,coset in left_cosets():
        fi=tuple(a if y in coset else Q(0) for (o,y),a in zip(X,f))
        parts.append((s,fi))
    assert total(fi for _,fi in parts)==f
    projected=scale(Q(1,len(K)),total(rho(mul(k,s),fi) for s,fi in parts for k in K))
    difference=scale(Q(1,len(K)),total(sub(rho(mul(k,s),fi),fi) for s,fi in parts for k in K))
    return projected,difference

def rank(vectors):
    """Sparse elimination over Q with first nonzero coordinate as pivot."""
    basis={}
    for v in vectors:
        a={i:Q(x) for i,x in enumerate(v) if x}
        while a:
            i=min(a); t=a[i]
            if i not in basis:
                basis[i]={j:x/t for j,x in a.items()};break
            for j,x in basis[i].items():
                vj=a.get(j,Q(0))-t*x
                if vj:a[j]=vj
                else:a.pop(j,None)
    return len(basis)

def group_test():
    # Basis tests give a complete linear test of the projection identity on this model.
    basis=[tuple(Q(int(i==j)) for i in range(len(X))) for j in range(len(X))]
    projections=[]
    for f in basis:
        pf=P(f); projections.append(pf)
        a,b=certificate(f)
        assert a==pf and b==sub(pf,f)
        assert P(pf)==pf and J(pf)==J(f)
    f=tuple(Q((i*i+5*i)%23-11,7) for i in range(len(X)))
    jf=J(f)
    for h in G:
        assert J(rho(h,f))==jf
        assert all(jf[index[o,mul(y,h)]]==chi(h)*jf[index[o,y]] for o,y in X)
    # All translation differences of basis vectors span ker(P).
    rkP=rank(projections)
    diffs=(sub(rho(h,f),f) for h in G for f in basis)
    rkD=rank(diffs)
    assert rkP==2 and rkD==len(X)-rkP
    # Example where point representative and average differ.
    delta=basis[index[0,I]]
    assert J(delta)[index[0,I]]==Q(1,len(K))
    print(f'GL2(F3): |G|={len(G)}, |K|={len(K)} (nonnormal), |X|={len(X)}')
    print(f'  {len(X)} basis vectors: exact projection, idempotence, J P = J, difference certificate PASS')
    print(f'  {len(G)} twisted translations: section invariance and covariance PASS')
    print(f'  rank(P)={rkP}; rank(span of differences)={rkD}; kernel equality PASS')

def dot(x,y,m): return sum(a*b for a,b in zip(x,y))%m

def complement_test(m):
    vectors=tuple(product(range(m),repeat=2))
    primitive=tuple(x for x in vectors if any(dot(x,z,m)==1 for z in vectors))
    pairs=completions=0
    for y in primitive:
        L=next(z for z in vectors if dot(z,y,m)==1)
        for x in primitive:
            if dot(x,y,m):continue
            # Test exactness; the theorem assumes it. In these rank-one cases it holds.
            ker={v for v in vectors if dot(x,v,m)==0}
            image={tuple(t*a%m for a in y) for t in range(m)}
            assert ker==image
            S=next(z for z in vectors if dot(x,z,m)==1)
            i=(y[0],S[0],y[1],S[1])
            row=tuple((L[j]-dot(L,S,m)*x[j])%m for j in range(2))
            ii=(*row,*x)
            assert mul(i,ii,m)==I and mul(ii,i,m)==I
            pairs+=1
            for T in vectors:
                if dot(x,T,m)==1:
                    j=(y[0],T[0],y[1],T[1])
                    assert det(i,m)==det(j,m)
                    assert mul(ii,j,m)[::3]==(1,1)
                    assert mul(ii,j,m)[2]==0
                    completions+=1
    print(f'Z/{m}Z: {pairs} complementary primitive pairs, {completions} integral completions: PASS')

def matching_test(m):
    """Full-space partner on primitive rank-one frames over a finite ring."""
    from math import gcd
    units=tuple(t for t in range(m) if gcd(t,m)==1)
    vectors=tuple(product(range(m),repeat=2))
    primitive=tuple(x for x in vectors if any(dot(x,z,m)==1 for z in vectors))
    scalev=lambda t,v:tuple(t*z%m for z in v)
    chi=lambda t:1 if t==1 else -1  # both Z/4 and Z/6 have two units
    def projection(f,v):
        return sum(chi(t)*f[scalev(t,v)] for t in units)/Q(len(units))
    mats=tuple(A for A in product(range(m),repeat=4) if det(A,m) in units)
    def row(A):return inv(A,m)[2:]
    def col(A):return (A[0],A[2])
    for q in primitive:  # arbitrary column basis data; verify by linearity
        f={v:Q(int(v==q)) for v in primitive}
        w={v:projection(f,v) for v in primitive}
        partner={}
        for A in mats:
            x,y=row(A),col(A)
            v=chi(det(A,m))*w[y]
            assert x not in partner or partner[x]==v
            partner[x]=v
        assert set(partner)==set(primitive)
        for x in primitive:
            assert projection(partner,x)==partner[x]
        recovered={}
        for A in mats:
            x,y=row(A),col(A)
            v=chi(det(A,m))*partner[x]
            assert v==w[y]
            recovered[y]=v
        assert recovered==w
    print(f'Z/{m}Z: matching map on {len(primitive)} column basis data; {len(mats)} integral matrices: PASS')

def local_shell_test():
    # Rank-one Q_3 model: units modulo 9, shell exponent j, character 3 -> 2
    # and unit character equal to the nontrivial character mod 3.
    U9=(1,2,4,5,7,8)
    def c(j,u): return Q(2)**j*(1 if u%3==1 else -1)
    def f(j,u): return Q((j*j+u*u+2*j*u)%13-4,5) if -2<=j<=2 else Q(0)
    def section(yj,yu):
        return sum(c(j-yj,u*pow(yu,-1,9)%9)*f(j,u)
                   for j in range(-2,3) for u in U9)/len(U9)
    ref=section(0,1)
    for j in range(-5,6):
        for u in U9:
            assert c(j,u)*section(j,u)==ref
    print('Q3 rank-one shell model: 66 cases, nonunitary character chi(3)=2: PASS')

if __name__=='__main__':
    group_test(); complement_test(4); complement_test(6); matching_test(4); matching_test(6); local_shell_test()
    print('All exact finite checks passed.')
