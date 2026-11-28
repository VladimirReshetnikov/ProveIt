#!/usr/bin/env python3
"""Exact finite certificates for the two constructions; no third-party dependencies."""
from itertools import combinations, product
from math import gcd, isqrt, prod, comb
from pathlib import Path
import json

def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))

def next_prime(n):
    while not prime(n): n += 1
    return n

def root_floor(x,k):
    lo,hi=0,1
    while hi**k<=x: hi*=2
    while hi-lo>1:
        m=(lo+hi)//2
        if m**k<=x: lo=m
        else: hi=m
    return lo

def centered(a,p):
    a%=p
    return a-p if 2*a>p else a

def short_lift(w,p):
    assert any(a%p for a in w)
    candidates=((tuple(centered(k*a,p) for a in w),k) for k in range(1,p))
    v,k=min(candidates,key=lambda item:(max(map(abs,item[0])),sum(a*a for a in item[0]),item[0]))
    H=root_floor(p**(len(w)-1),len(w))
    assert max(map(abs,v))<=H and any(a%p for a in v)
    assert all((a-k*b)%p==0 for a,b in zip(v,w))
    return v,k

def determinant(rows):
    # Fraction-free elimination, pivoting with exact division.
    a=[list(row) for row in rows]; n=len(a); sign=1; prev=1
    if n==0: return 1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None: return 0
        if pivot!=k: a[k],a[pivot]=a[pivot],a[k]; sign=-sign
        d=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                x=a[i][j]*d-a[i][k]*a[k][j]
                assert x%prev==0
                a[i][j]=x//prev
            a[i][k]=0
        prev=d
    return sign*a[-1][-1]

def det_cols(cols): return determinant(list(zip(*cols)))

def curve(t,r,p): return tuple(pow(t,j,p) for j in range(r))

def statistics(cols,p,parameters,scalars,expected_delta=None):
    r=len(cols[0]); n=len(cols); D=0; S=0; maximum=0; nmax=0; minimum=None
    for ix in combinations(range(n),r):
        d=det_cols([cols[i] for i in ix]); ad=abs(d)
        assert d!=0
        if expected_delta is not None:
            if ix==tuple(range(r)):
                assert d==expected_delta
            else:
                assert 2*ad<=expected_delta
        D=gcd(D,ad); S+=d*d
        if ad>maximum: maximum,nmax=ad,1
        elif ad==maximum: nmax+=1
        minimum=ad if minimum is None else min(minimum,ad)
    G=[[sum(v[i]*v[j] for v in cols) for j in range(r)] for i in range(r)]
    assert determinant(G)==S and S%(D*D)==0
    return dict(rank=r,n=n,prime=p,minor_count=comb(n,r),gcd=D,min_minor=minimum,max_minor=maximum,
                max_minor_count=nmax,gram=G,gram_det=S,normalized_gram=S//D**2,
                columns=cols,parameters=parameters,scalars=scalars)

def check_modular(cols,p,parameters,scalars,factor):
    # Separately verify each maximal minor using modular Vandermonde.
    for ix in combinations(range(len(cols)),len(cols[0])):
        expected=factor*prod(scalars[i] for i in ix)*prod(parameters[j]-parameters[i] for i,j in combinations(ix,2))
        assert det_cols([cols[i] for i in ix])%p==expected%p!=0

def gram_example(r,n):
    p=next_prime(n); ts=list(range(n)); pairs=[short_lift(curve(t,r,p),p) for t in ts]
    cols,scalars=map(list,zip(*pairs)); H=root_floor(p**(r-1),r)
    rec=statistics(cols,p,ts,scalars); check_modular(cols,p,ts,scalars,1)
    assert rec['gram_det']<=n**r*H**(2*r)
    assert rec['max_minor']**2<=r**r*H**(2*r)
    rec['H']=H; rec['constructive_gram_upper']=n**r*H**(2*r)
    return rec

def inverse_mod(rows,p):
    n=len(rows); a=[[v%p for v in row]+[int(i==j) for j in range(n)] for i,row in enumerate(rows)]
    for j in range(n):
        k=next(i for i in range(j,n) if a[i][j]); a[j],a[k]=a[k],a[j]
        t=pow(a[j][j],-1,p); a[j]=[(x*t)%p for x in a[j]]
        for i in range(n):
            if i!=j:
                t=a[i][j]; a[i]=[(x-t*y)%p for x,y in zip(a[i],a[j])]
    return [row[n:] for row in a]

def matmul(A,B,p): return [[sum(x*y for x,y in zip(row,col))%p for col in zip(*B)] for row in A]

def anchor_matrix(r,delta):
    b=root_floor(delta,r)+1; digits=[]; tmp=delta
    for _ in range(r): digits.append(tmp%b); tmp//=b
    assert tmp==0
    cols=[tuple(b if i==j else -1 if i==j+1 else 0 for i in range(r)) for j in range(r-1)]+[tuple(digits)]
    assert det_cols(cols)==delta
    return b,cols

def exact_delta(r,delta,p):
    assert prime(p) and p>=r and delta%p
    b,B=anchor_matrix(r,delta); H=root_floor(p**(r-1),r)
    assert H<=b and r**r*b**(2*(r-1))*H**2<delta**2  # strict Hadamard bound
    V=list(zip(*(curve(t,r,p) for t in range(r))))
    T=matmul(list(zip(*B)),inverse_mod(V,p),p)
    assert matmul(T,V,p)==[[a%p for a in row] for row in zip(*B)]
    cols=list(B); scalars=[1]*r
    for t in range(r,p):
        w=tuple(sum(a*z for a,z in zip(row,curve(t,r,p)))%p for row in T)
        v,k=short_lift(w,p); cols.append(v); scalars.append(k)
    rec=statistics(cols,p,list(range(p)),scalars,expected_delta=delta)
    check_modular(cols,p,list(range(p)),scalars,determinant(T)%p)
    assert rec['max_minor']==delta and rec['max_minor_count']==1
    rec.update(delta=delta,base=b,H=H,transform=T,anchor_columns=B,
               other_minor_square_upper=r**r*b**(2*(r-1))*H**2)
    return rec

def box_example(L):
    L=sorted(L); r=len(L); C=r+1
    Ps={j:prod(L[:j]) for j in range(2,r+1)}
    # Choose j with smallest P_j^(1/(j-1)), by exact cross-power comparisons.
    j=2
    for k in range(3,r+1):
        if Ps[k]**(j-1)<Ps[j]**(k-1): j=k
    P=Ps[j]; e=j-1; assert P>=L[j-1]**e
    ms=[root_floor(C**e*P//l**e,e) for l in L[:j]]
    assert prod(m+1 for m in ms)>sum(m*l for m,l in zip(ms,L[:j]))+1
    coeffs=list(product(*(range(m+1) for m in ms)))
    normals=set(); count=0
    # Check all points in the complete box, not a random sample.
    for z in product(*(range(-l,l+1) for l in L)):
        seen={}; found=False
        for a in coeffs:
            dot=sum(x*y for x,y in zip(a,z))
            if dot in seen:
                u=tuple(x-y for x,y in zip(a,seen[dot]))+(0,)*(r-j)
                assert any(u) and sum(x*y for x,y in zip(u,z))==0
                normals.add(u); found=True; break
            seen[dot]=a
        assert found; count+=1
    assert len(normals)**(r-1)<=(2*r+3)**(r*(r-1))*prod(L)
    return dict(halfwidths=L,j=j,R_power=P,R_exponent=e,coefficient_bounds=ms,
                checked_points=count,realized_normals=len(normals))

def main():
    gram=[gram_example(r,n) for r,n in [(2,12),(2,48),(3,12),(3,32),(3,64),(4,12),(4,30),(5,17),(5,23)]]
    exact=[exact_delta(r,d,p) for r,d,p in [(2,100003,101),(3,1000001,31),(4,1000000000039,31),(5,1000000000000037,17)]]
    boxes=[box_example(L) for L in [(2,3),(1,1,10),(1,2,4),(2,3,4,7),(1,1,1,1,50),(2,2,3),(1,3,5,8)]]
    out=Path(__file__).resolve().parents[1]/'data'/'verification.json'
    out.write_text(json.dumps({'gram_examples':gram,'exact_delta_examples':exact,'box_examples':boxes},indent=2)+'\n')
    for x in gram:
        print('Gram',x['rank'],x['n'],x['prime'],x['H'],x['gcd'],x['normalized_gram'],x['max_minor'])
    for x in exact:
        print('Exact',x['rank'],x['delta'],x['n'],x['max_minor_count'],x['H'])
    print('Checked',sum(x['minor_count'] for x in gram+exact),'maximal minors in each of two exact passes; ',sum(x['checked_points'] for x in boxes),'box points.')
    print('PASS')
if __name__=='__main__': main()
