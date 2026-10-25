#!/usr/bin/env python3
"""Exact sparse-polynomial exploration; Python standard library only."""
from fractions import Fraction as F
N=4
WEIGHTS=(1,3,1,5)
class Poly(dict):
    def __init__(self,v=0):
        if isinstance(v,dict): super().__init__({m:F(c) for m,c in v.items() if c})
        else: super().__init__({(0,)*N:F(v)} if v else {})
    def __add__(self,other):
        if not isinstance(other,Poly):other=Poly(other)
        d=dict(self)
        for m,c in other.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.items()})
    def __sub__(self,other):return self+-Poly(other)
    def __rsub__(self,other):return Poly(other)+-self
    def __mul__(self,other):
        if not isinstance(other,Poly):other=Poly(other)
        d={}
        for m,c in self.items():
            for e,b in other.items():
                v=tuple(x+y for x,y in zip(m,e))
                d[v]=d.get(v,0)+c*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,p):
        v=Poly(1)
        for _ in range(p):v=v*self
        return v
    def degree(self):return max((sum(x*y for x,y in zip(m,WEIGHTS)) for m in self),default=-1)
    def __str__(self):
        out=[]
        for m in sorted(self,reverse=True):
            c=self[m]
            term='*'.join(v+(f'^{p}' if p!=1 else '') for v,p in zip(('L','t','k','E'),m) if p)
            out.append(f'{c}'+('*'+term if term else ''))
        return ' + '.join(out) or '0'
def var(i):return Poly({tuple(int(j==i) for j in range(N)):1})
L,t,k,E=[var(i) for i in range(N)]
A=L*t+1
D=k*k*((L-1)**2*t**4+(L-1)*t*t)+1

def div(poly,power):
    q=Poly(); terms=dict(poly); divisor=A**power; out={}
    while terms:
        m=max(terms,key=lambda e:sum(x*y for x,y in zip(e,WEIGHTS)))
        c=terms[m]
        if m[0]>=power and m[1]>=power:
            shift=(m[0]-power,m[1]-power,m[2],m[3]); q=q+Poly({shift:c})
            for e,b in divisor.items():
                v=tuple(x+y for x,y in zip(e,shift)); terms[v]=terms.get(v,0)-c*b
                if not terms[v]: del terms[v]
        else:out[m]=terms.pop(m)
    r=Poly(out); assert not (poly-q*A**power-r)
    return q,r

def binomhalf(j):
    a=F(1)
    for i in range(j):a*=F(1,2)-i;a/=i+1
    return a

def make(m,n):
    W=L**m*t**n; C=W*D*A; qs=[]
    for j in range(1,1+min(m+2,n+4)//2+2):
        odd=2*j-1; q,r=div(W*D,odd)
        if not q:break
        coeff=binomhalf(j)*(-1)**j; C=C+coeff*q; qs.append((odd,coeff,q,r))
    residual=E**2*(C*C-W*W*D*D*(A*A-1))-W*W*D
    return C,residual,qs

if __name__=='__main__':
    rows=[]
    for n in range(5):
        for m in range(9):
            c,r,qs=make(m,n); rows.append((r.degree(),m,n,len(qs),c.degree()+5))
    for row in sorted(rows): print(row)
    for m,n in [(0,0),(1,0),(2,0),(3,0),(4,0)]:
        c,r,qs=make(m,n); print('PROFILE',m,n,'residual_degree',r.degree())
        for o,coef,q,r in qs: print('q',o,coef,q,'r',r)
