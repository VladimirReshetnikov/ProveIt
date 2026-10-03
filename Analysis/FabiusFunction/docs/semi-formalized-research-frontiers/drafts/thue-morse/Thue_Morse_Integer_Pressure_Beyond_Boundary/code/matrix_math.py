"""Exact response and pressure triangles, with independent phase-jet checks."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'data'

def R(k):
    return (-1)**(k+1)*2**(2*k)*(2**(2*k)-1)*s.bernoulli(2*k)/s.factorial(2*k)

def matrix_jets(m,N,normalized):
    ix=list(range(1-m,m));d=len(ix)
    def base(k,r):
        j=2*k-r
        return 2*s.Rational(s.binomial(2*m,m+j),4**m) if abs(j)<=m else s.S.Zero
    V=s.Matrix(d,d,lambda k,r:base(ix[k],ix[r]))
    matrices=[]
    for n in range(N+1):
        def entry(k,r):
            j=2*ix[k]-ix[r]
            if abs(j)>m:return s.S.Zero
            if normalized:
                q=sum((-1)**h*s.binomial(m+j,h)*s.binomial(m-j,n-h)for h in range(n+1))
            else:q=s.Rational((-2*j)**n,s.factorial(n))
            return V[k,r]*q
        matrices.append(s.Matrix(d,d,entry))
    A=s.eye(d)-V;C=A.copy();C[0,:]=s.ones(1,d);inv=C.inv()
    rhs=s.zeros(d,1);rhs[0]=1
    vectors=[inv*rhs];eigen=[s.S.One]
    assert A*vectors[0]==s.zeros(d,1) and sum(vectors[0])==1
    for n in range(1,N+1):
        b=sum((matrices[j]*vectors[n-j]for j in range(1,n+1)),s.zeros(d,1))
        eigen.append(sum(b))
        target=b-sum((eigen[j]*vectors[n-j]for j in range(1,n+1)),s.zeros(d,1))
        assert sum(target)==0
        rhs=target.copy();rhs[0]=0;vn=inv*rhs
        assert A*vn==target and sum(vn)==0
        vectors.append(vn)
    return ix,vectors,eigen

def mul(a,b,N):
    c=[s.S.Zero]*(N+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:N+1-i]):c[i+j]+=x*y
    return c

def tan_relative_power(power,N):
    f=[R(j+1)for j in range(N+1)];out=[s.S.One]+[s.S.Zero]*N
    for _ in range(power):out=mul(out,f,N)
    return out

def pressure_from_responses(m,H):
    out=[]
    for r in range(1,m):
        value=sum(H[j]*tan_relative_power(2*m+2*j,r-j)[r-j]for j in range(r+1))
        value-=s.Rational(m,m+r)*R(m+r)
        out.append(s.factor(value))
    return out

def direct_pressure(m,N):
    _,_,eigen=matrix_jets(m,N,False)
    assert all(eigen[n]==0 for n in range(1,N+1,2))
    lam=[eigen[n]*(-1)**(n//2)if n%2==0 else s.S.Zero for n in range(N+1)]
    p=[s.S.Zero]
    for n in range(1,N+1):
        p.append(s.factor(lam[n]-sum(k*p[k]*lam[n-k]for k in range(1,n))/n))
    assert p[2*m]==0
    return p
