#!/usr/bin/env python3
"""Exact finite bias/collision certificates and a numerical LP example.
Run: python check_examples.py   (requires numpy, scipy only for the LP)
No GRH assumption is used by these finite computations.
"""
from fractions import Fraction as F
from math import isqrt, gcd
from random import Random
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q, X, K = 24, 4096, 2
# The units of Z/24Z are (C2)^3, with independent generators 5,7,13.
G = {pow(5, i & 1, Q)*pow(7, (i>>1)&1, Q)*pow(13, (i>>2)&1, Q)%Q:i for i in range(8)}
assert len(G)==8

def prime_list(n):
    a=bytearray(b'\x01')*(n+1); a[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p:n+1:p]=b'\0'*((n-p*p)//p+1)
    return [i for i in range(2,n+1) if a[i]]

def row(p):
    b=G[p%Q]
    return [(-1)**((b&j).bit_count()) for j in range(8)]

def show(name, x):
    print(f'{name}: {x} ({float(x):.10f})' if isinstance(x,F) else f'{name}: {x}')

def certify(P, W, label):
    T=sum(W); A=[row(p) for p in P]
    b=[F(sum(w*a[j] for a,w in zip(A,W)),T) for j in range(1,8)]
    delta=max(map(abs,b)); mu_max=F(max(W),T)
    print('\n'+label); show('number of distinct primes',len(P)); show('bias delta',delta); show('max atom',mu_max)
    # Choose a corruption set of weight <= 9/100; largest weights first.
    order=sorted(range(len(P)),key=lambda i:-W[i]); E=[]; mass=0
    for i in order:
        if 100*(mass+W[i])<=9*T: E.append(i);mass+=W[i]
    alpha=F(mass,T); margin=1-2*K*delta-4*K*alpha
    show('corrupted samples',len(E));show('alpha',alpha);show('certificate margin',margin)
    assert margin>0
    show('calibrated margin',1-(2*K-1)*delta-4*K*alpha)
    # Collision using the subgroup H of character indices {0,1,2,3}.
    # Pick a lightest coset of H^perp, indexed by the low 2 bits.
    cosets=[[i for i,p in enumerate(P) if G[p%Q]&3==b] for b in range(4)]
    C=min(cosets,key=lambda ids:sum(W[i] for i in ids)); b=(G[P[C[0]]%Q]&3) if C else cosets.index(C)
    phase=[(-1)**((b&j).bit_count()) for j in range(4)]
    c1=phase[:2]+[0]*6;c2=[0,0,-phase[2],-phase[3],0,0,0,0]
    f1=[sum(u*v for u,v in zip(a,c1)) for a in A]; f2=[sum(u*v for u,v in zip(a,c2)) for a in A]
    assert [i for i,(u,v) in enumerate(zip(f1,f2)) if u!=v]==C
    assert sum(W[i] for i in C)*4<=T
    B1=[];B2=[];s1=s2=0
    for i in sorted(C,key=lambda i:-W[i]):
        if s1<=s2:B1.append(i);s1+=W[i]
        else:B2.append(i);s2+=W[i]
    y=f1[:]
    for i in B1:y[i]=f2[i]
    assert [i for i,v in enumerate(y) if v!=f1[i]]==sorted(B1)
    assert [i for i,v in enumerate(y) if v!=f2[i]]==sorted(B2)
    radius=F(max(s1,s2),T);assert radius<=F(1,8)+mu_max/2
    show('ambiguous observation error radius',radius)
    return A,E,delta,alpha,margin

def numerical_lp(A,W,E,delta=F(0)):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import eye, csr_matrix, hstack, vstack
    A=np.asarray(A,dtype=float);m,n=A.shape; mu=np.asarray([float(F(w,sum(W))) for w in W]); c=np.zeros(n);c[0]=2;c[3]=-3
    y=A@c
    for j,i in enumerate(E):y[i]+=(-1)**j*(10000+j)
    # variables z+ >=0, z- >=0, residual magnitudes t>=0
    B=csr_matrix(A); I=eye(m,format='csr');
    constr=vstack([hstack([B,-B,-I]),hstack([-B,B,-I])],format='csr')
    obj=np.r_[np.ones(2*n),float(F(2*K)/(1+delta))*mu]
    res=linprog(obj,A_ub=constr,b_ub=np.r_[y,-y],bounds=(0,None),method='highs')
    assert res.success,res.message
    z=res.x[:n]-res.x[n:2*n];err=np.sum(np.abs(z-c));show('LP reconstruction',z.tolist());show('LP l1 error',err);assert err<1e-6

if __name__=='__main__':
    P=[p for p in prime_list(2*X) if X<p<2*X and gcd(p,Q)==1]
    W=[(p-X)**3*(2*X-p)**3 for p in P];assert min(W)>0
    A,E,delta,*_=certify(P,W,'Weighted deterministic window')
    print('Calibrated decoder:')
    numerical_lp(A,W,E,delta)
    print('Uncalibrated decoder:')
    numerical_lp(A,W,E)
    # Exact Bernoulli thinning with fixed PRNG seed; the observed bias is
    # certified after selection. This is illustrative, not the conservative
    # asymptotic sample-size bound from the theorem.
    r=Random(20261127); target=200;T=sum(W);assert target*max(W)<=T
    S=[p for p,w in zip(P,W) if r.randrange(T)<target*w]
    certify(S,[1]*len(S),'Unweighted thinned pool')
    with open(HERE/'prime_pools.csv','w',newline='') as f:
        out=csv.writer(f);out.writerow(['prime','residue_mod_24','integer_weight','in_thinned_pool'])
        ss=set(S);out.writerows((p,p%Q,w,int(p in ss)) for p,w in zip(P,W))
    # Exact finite-bias extremizer, with two equal-mass copies of each unit.
    d=F(1,20); r=2*K; n=len(G)
    residues=sorted(G)
    mu=[(1-(r-1)*d)/n if G[g]&3==0 else (1+d)/n for g in residues]
    assert sum(mu)==1 and min(mu)>0
    assert max(abs(sum(w*row(g)[j] for w,g in zip(mu,residues))) for j in range(1,n))==d
    distance=sum(w for w,g in zip(mu,residues) if G[g]&3==0)
    assert distance==(1-(r-1)*d)/r
    show('Exact abstract extremizer bias',d)
    show('Exact abstract extremizer ambiguity radius',distance/2)
    print('\nAll exact finite checks passed; LP checks are numerical.')
