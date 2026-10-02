#!/usr/bin/env python3
"""Exact finite checks over Q(sqrt(2)); standard Python only.
Checks are examples and normalization audits, not a proof of the limit theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path

@dataclass(frozen=True)
class F:
    a: Q = Q(0)
    b: Q = Q(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))
    @staticmethod
    def of(x): return x if isinstance(x, F) else F(x)
    def __add__(self, y):
        y=F.of(y); return F(self.a+y.a, self.b+y.b)
    __radd__=__add__
    def __neg__(self): return F(-self.a,-self.b)
    def __sub__(self,y): return self+-F.of(y)
    def __rsub__(self,y): return F.of(y)+-self
    def __mul__(self,y):
        y=F.of(y); return F(self.a*y.a+2*self.b*y.b,self.a*y.b+self.b*y.a)
    __rmul__=__mul__
    def __truediv__(self,y):
        y=F.of(y); d=y.a*y.a-2*y.b*y.b
        if not d: raise ZeroDivisionError
        return self*F(y.a/d,-y.b/d)
    def __rtruediv__(self,y): return F.of(y)/self
    def __pow__(self,n):
        if n<0: return (1/self)**(-n)
        result=F(1); x=self
        while n:
            if n&1: result=result*x
            x=x*x; n//=2
        return result
    def positive(self):
        a,b=self.a,self.b
        if b==0: return a>0
        if a==0: return b>0
        if a>0 and b>0: return True
        if a<0 and b<0: return False
        if a>0: return a*a>2*b*b
        return 2*b*b>a*a
    def serial(self): return {'rational':str(self.a),'sqrt2_coefficient':str(self.b)}


def ldl(matrix):
    a=[list(row) for row in matrix]; n=len(a); h=[]
    for k in range(n):
        p=a[k][k]; assert p.positive(); h.append(p)
        for i in range(k+1,n):
            t=a[i][k]/p
            for j in range(i,n): a[j][i]=a[j][i]-t*a[j][k]
    return h


def mul(p,q):
    r=[F() for _ in range(len(p)+len(q)-1)]
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]=r[i+j]+x*y
    return r


def bareiss_det(a):
    a=[list(row) for row in a]; prev=1
    for k in range(len(a)-1):
        pivot=a[k][k]; assert pivot>0
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                num=pivot*a[i][j]-a[i][k]*a[k][j]
                assert num%prev==0; a[i][j]=num//prev
        prev=pivot
    return a[-1][-1] if a else 1


def main(n=6):
    A=[sum(comb(k,j)**2*comb(k+j,j)**2 for j in range(k+1))
       for k in range(2*n+3)]
    for k in range(1,len(A)-1):
        assert (k+1)**3*A[k+1]==(34*k**3+51*k*k+27*k+5)*A[k]-k**3*A[k-1]
    C=F(17,12); lam=C/4
    m=[F(a)/C**k for k,a in enumerate(A)]
    variants=[m,[m[k+1] for k in range(2*n+1)],
              [m[k]-m[k+1] for k in range(2*n+1)],
              [m[k+1]-m[k+2] for k in range(2*n+1)]]
    h,ht,hu,hr=[ldl([[v[i+j] for j in range(n+1)] for i in range(n+1)])
                for v in variants]
    # Circle moments are integrals of T_j(2t-1), computed independently.
    cheb=[[F(1)],[F(-1),F(2)]]
    for j in range(1,2*n+1):
        p=mul([F(-2),F(4)],cheb[-1])
        for k,v in enumerate(cheb[-2]):p[k]=p[k]-v
        cheb.append(p)
    nu=[sum((v*m[k] for k,v in enumerate(p)),F()) for p in cheb]
    e=ldl([[nu[abs(i-j)] for j in range(2*n+2)] for i in range(2*n+2)])
    E=[F(2)]; alphas=[]
    for k in range(n+1):
        if k:
            U=16**k*h[k]; V=16**k*hr[k-1]
            E.append(2*U*V/(U+V)); alphas.append((U-V)/(U+V))
        X=4*16**k*ht[k]; Y=4*16**k*hu[k]
        E.append(2*X*Y/(X+Y)); alphas.append((X-Y)/(X+Y))
    assert len(E)==2*n+2
    for j in range(len(E)):
        assert E[j]==2*e[j]
        if j:
            assert E[j]==E[j-1]*(1-alphas[j-1]**2)
            assert E[j-1]==E[j] or (E[j-1]-E[j]).positive()
    Ds=[]; product=F(1)
    for k in range(n+1):
        product=product*h[k]*C**(2*k)
        D=bareiss_det([[A[i+j] for j in range(k+1)] for i in range(k+1)])
        assert product==F(D); Ds.append(D)
    prefix=[1,48,161856,39002646528,674708032182398976,
            839431510934341028210638848,
            75178263784150214825106859877233852416]
    assert Ds==prefix[:n+1]
    report={'status':'PASS: all equalities and positivity checks exact in Q(sqrt(2))',
            'max_hankel_degree':n,'toeplitz_orders_checked':len(E),
            'norm_recurrences_checked':len(alphas),
            'independent_bareiss_determinants':len(Ds),
            'determinants':Ds,'E1':E[1].serial(),'E2':E[2].serial(),
            'last_upper_envelope':E[-1].serial()}
    return report

if __name__=='__main__':
    report=main()
    root=Path(__file__).resolve().parents[1]
    (root/'data'/'exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='last_upper_envelope'},indent=2))
