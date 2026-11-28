#!/usr/bin/env python3
"""Finite-jet replay over prime fields and a sample of quadratic extensions."""
from math import isqrt

def check(p, d, parameters):
    # a+p*b encodes a+b*sqrt(d); prime-field elements have b=0.
    def add(x,y): return (x%p+y%p)%p + p*((x//p+y//p)%p)
    def mul(x,y):
        a,b= x%p,x//p
        c,e= y%p,y//p
        return (a*c+d*b*e)%p + p*((a*e+b*c)%p)
    def neg(x): return mul(p-1,x)
    def conv(a,b,k):
        c=[0]*k
        for i,x in enumerate(a[:k]):
            if x:
                for j,y in enumerate(b[:k-i]):
                    if y: c[i+j]=add(c[i+j],mul(x,y))
        return c
    def powpoly(a,n,k):
        c=[1]+[0]*(k-1)
        while n:
            if n&1: c=conv(c,a,k)
            n//=2
            if n: a=conv(a,a,k)
        return c
    def derivative(a): return [mul(i%p,a[i]) for i in range(1,len(a))]
    m=(p-1)//2
    counts=[0,0,0]
    for A in parameters:
        # Independently generate x from x''=2+4Ax+6x² for degrees <p.
        # Put x_p=x_(p+1)=0. The square ODE obstruction at degree p+1
        # is independent of x_(p+1) modulo p.
        x=[0]*(p+2);x[2]=1
        for i in range(4,p,2):
            j=i-2
            h=0
            for l in range(j+1): h=add(h,mul(x[l],x[j-l]))
            x[i]=mul(add(mul(4%p,mul(A,x[j])),mul(6%p,h)),pow((i*(i-1))%p,-1,p))
        c=powpoly([1,A,1],m,m+1)
        xx=conv(x,x,p+2)
        Q=[add(mul(A,z),w) for z,w in zip(x,xx)];Q[0]=1
        a=conv(derivative(x),derivative(x),p+2)
        b=[mul(4%p,w) for w in conv(x,Q,p+2)]
        assert a[:-1]==b[:-1]
        assert (a==b)==(c[m]==0)
        t=[0]+powpoly(x[2:],m+1,p)
        tsq=conv(t,t,p+2)
        assert tsq==x
        TQ=[add(mul(A,z),w) for z,w in zip(tsq,conv(tsq,tsq,p))];TQ[0]=1
        prod=conv(derivative(t),powpoly(TQ,m,p),p)
        assert prod[:-1]==[1]+[0]*(p-2)
        assert (prod[-1]==0)==(c[m]==0)
        for n in range(1,m+1):
            assert powpoly(x,n,p)[p-1]==c[m-n]
            counts[0]+=1
        if c[m]==0:
            counts[1]+=1
            assert c[m-1]!=0
            assert powpoly(x,0,p)[p-1]==c[m]
        counts[2]+=1
    return counts

prime=[p for p in range(3,74,2) if all(p%d for d in range(3,isqrt(p)+1,2))]
tot=[0,0,0]
for p in prime:
    ans=check(p,0,range(p))
    tot=[a+b for a,b in zip(tot,ans)]
print("Prime fields: %d positive-power coefficients; %d vanishing-central cases; %d parameters"%tuple(tot))
tot=[0,0,0]
for p in prime[:7]:
    d=next(d for d in range(2,p) if pow(d,(p-1)//2,p)==p-1)
    ans=check(p,d,range(p*p))
    tot=[a+b for a,b in zip(tot,ans)]
print("Quadratic fields: %d positive-power coefficients; %d vanishing-central cases; %d parameters"%tuple(tot))
