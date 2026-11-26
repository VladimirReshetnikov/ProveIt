#!/usr/bin/env python3
"""Exact rational calculation of finite Lubin--Tate coefficient-depth modules.
Unlike the published Appendix A code, insert only genuine trace-kernel rows.
No p-adic floating precision is used. Rational Z_(p) elimination is exact;
extension to O_{Q_{p^2}} is faithfully flat and preserves pivot valuations.
"""
from fractions import Fraction as F
from math import comb
import json, argparse

def vp(x,p):
    if not x: return float('inf')
    x=F(x); a,b=x.numerator,x.denominator; v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    return v

def convolution(a,b,N):
    c=[F(0) for _ in range(N+1)]
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:N+1-i]):
                if y:c[i+j]+=x*y
    return c

def logs(p,N):
    q=p*p
    L=[F(0) for _ in range(N+1)];L[1]=F(1)
    for n in range(2,N+1):
        if (n-1)%(q-1):continue
        L[n]=sum((L[n-i*(q-1)]*comb(n-i*(q-1),i)*p**(n-i*q) for i in range(1,n//q+1)),F(0))/(p-p**n)
    return L

def setup(p,N):
    q=p*p; L=logs(p,N)
    D=[[F(0) for _ in range(N+1)] for _ in range(N+1)];D[0][0]=F(1)
    for i in range(1,N+1):D[i]=convolution(D[i-1],L,N)
    E=[[F(0) for _ in range(N+1)] for _ in range(N+1)]
    for i in range(N+1):
        E[i][i]=F(1)
        for j in range(i+q-1,N+1,q-1):
            E[i][j]=-sum((E[i][k]*D[k][j] for k in range(i,j,q-1)),F(0))
    phi=[F(0) for _ in range(N+1)];phi[1]=F(p)
    if q<=N:phi[q]=F(1)
    powers=[[F(0) for _ in range(N+1)]];powers[0][0]=F(1)
    for j in range(1,N+1):powers.append(convolution(powers[-1],phi,N))
    generators=[]
    for j in range(N+1):
        f=[(q-1)*x for x in powers[j]]
        for n in range(q-1,N+1):f[n]+=p*powers[j][n-(q-1)]
        generators.append((f'kernel_{j}',f))
        for i in range(1,q-1):
            if i+j<=N:generators.append((f'monomial_{i}_{j}',[F(0)]*i+powers[j][:N+1-i]))
    H=[]
    for name,f in generators:
        nz=[(i,x) for i,x in enumerate(f) if x]
        h=[sum((x*E[i][n] for i,x in nz if i<=n),F(0)) for n in range(N+1)]
        H.append((name,h))
    return D,H

def add_row(basis,row,p):
    row=row[:]
    while any(row):
        j=max(i for i,x in enumerate(row) if x)
        if j not in basis:
            basis[j]=row;return
        if vp(row[j],p)<vp(basis[j][j],p):basis[j],row=row,basis[j]
        c=row[j]/basis[j][j]
        assert vp(c,p)>=0
        row=[x-c*y for x,y in zip(row,basis[j])]

def wq(n,q):
    s=0
    while n:n//=q;s+=n
    return s

def run(p,N):
    D,H=setup(p,N);basis={};res={};counts=[]
    for m in range(N+1):
        count=0
        for name,h in H:
            row=[h[n]*D[n][m] if n<=m else F(0) for n in range(N+1)]
            if any(row):add_row(basis,row,p);count+=1
        counts.append(count)
        for n,b in basis.items():
            if n not in res and vp(b[n],p)==-wq(n,p*p):res[n]=m
    return {'p':p,'q':p*p,'cutoff':N,'s0':{str(n):res.get(n) for n in range(N+1)},'final_pivot_valuations':{str(n):vp(basis[n][n],p) if n in basis else None for n in range(N+1)},'new_generator_counts':counts}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--p',type=int,default=2);ap.add_argument('--cutoff',type=int,default=24);ap.add_argument('--out');a=ap.parse_args()
    result=run(a.p,a.cutoff)
    txt=json.dumps(result,indent=2)
    if a.out:open(a.out,'w').write(txt+'\n')
    print(txt)
