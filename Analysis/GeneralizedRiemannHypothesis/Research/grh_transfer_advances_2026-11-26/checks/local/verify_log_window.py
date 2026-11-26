#!/usr/bin/env python3
"""Finite-ring verification of the exact Lubin--Tate logarithm coefficient lemma."""
from math import comb
import json

def vp(n,p):
    if not n:return 10**9
    v=0
    while n%p==0:n//=p;v+=1
    return v

def mul(a,b,J,mod):
    c=[0]*(J+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:J+1-i]):c[i+j]=(c[i+j]+x*y)%mod
    return c

def power(a,n,J,mod):
    r=[1]+[0]*J
    while n:
        if n%2:r=mul(r,a,J,mod)
        n//=2
        if n:a=mul(a,a,J,mod)
    return r

def verify(p,f=2,nmax=128,jmax=64):
    q=p**f; a=q-1; precision=20; modulus=p**precision
    lam=[1]+[0]*jmax
    for j in range(1,jmax+1):
        num=sum(lam[i]*pow(p,a*i,modulus)*comb(1+a*i,j-i) for i in range(j) if j-i<=1+a*i)
        lam[j]=num*pow(1-pow(p,a*j,modulus),-1,modulus)%modulus
    assert lam[1]* (1-p**a)%modulus==1
    assert all(x%p**a==0 for x in lam[2:])
    checks=0
    for n in range(1,nmax+1):
        N=vp(n,p); J=min(p**N,jmax)
        coeff=power(lam[:J+1],n,J,modulus)
        for j in range(1,J+1):
            target=N-vp(j,p)
            assert vp(coeff[j],p)==target,(p,n,j,coeff[j],target)
            checks+=1
    return {'p':p,'f':f,'q':q,'n_max':nmax,'j_max':jmax,'precision':precision,'checks':checks,'status':'passed'}

if __name__=='__main__':
    result={'checks':[verify(p,f) for p,f in ((2,1),(2,2),(2,3),(3,1),(3,2),(5,2),(7,2))],'interpretation':'Exact modular checks of scaled coefficient valuations; universal proof is in log_window.tex.'}
    print(json.dumps(result,indent=2))
