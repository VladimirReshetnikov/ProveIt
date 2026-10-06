#!/usr/bin/env python3
"""Exact rational profile and inverse algorithms, at arbitrary fixed order.

Two independent formal routes regenerate the h-series: the split W-kernel
and the symmetric endpoints of the V recurrence. Central moments are built
from factorial moments, then cross-checked against the cumulant recurrence.
No symbolic packages, sequence fitting, floating point, or file writes.
"""
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True


from fractions import Fraction as F
from math import comb, factorial
import argparse
import json


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def mul(a,b,degree):
    c=[F(0)]*(degree+1)
    for i,x in enumerate(a[:degree+1]):
        for j,y in enumerate(b[:degree+1-i]):
            c[i+j]+=x*y
    return c


def add(a,b,degree):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(degree+1)]


def reciprocal(a,degree):
    need(a[0]!=0,'zero constant in reciprocal')
    result=[1/a[0]]
    for i in range(1,degree+1):
        result.append(-sum(a[j]*result[i-j] for j in range(1,min(i+1,len(a))))/a[0])
    return result


def power(a,n,degree):
    need(type(n) is int and n>=0,'nonnegative integer power required')
    result=[F(1)]+[F(0)]*degree
    for _ in range(n):
        result=mul(result,a,degree)
    return result


def shifted(a,shift,degree):
    result=[F(a[0])]+[F(0)]*degree
    for i in range(1,min(degree+1,len(a))):
        for j in range(degree-i+1):
            result[i+j]+=a[i]*comb(i+j-1,j)*shift**j
    return result


def exp_series(a,degree):
    need(a[0]==0,'exponential must have zero constant')
    result=[F(1)]
    for n in range(1,degree+1):
        result.append(sum(j*a[j]*result[n-j] for j in range(1,n+1))/n)
    return result


def binomial(a,n):
    result=F(1)
    for j in range(n):
        result*=F(a-j,j+1)
    return result


def bernoulli(limit):
    result=[F(1)]
    for n in range(1,limit+1):
        result.append(-sum(comb(n+1,j)*result[j] for j in range(n))/(n+1))
    return result


def central_moments(degree):
    p=F(2,3)
    S=[[1]]
    falling=[[F(1)]+[F(0)]*degree]
    raw=[]
    for n in range(1,degree+1):
        prev=S[-1]
        S.append([(prev[k-1] if k else 0)+(k*prev[k] if k<len(prev) else 0) for k in range(n+1)])
        falling.append(mul(falling[-1], [F(1-n),F(1)],degree))
    for n in range(degree+1):
        raw.append([sum(S[n][k]*p**k*falling[k][i] for k in range(n+1)) for i in range(degree+1)])
    moments=[]
    for d in range(degree+1):
        row=[F(0)]*(degree+1)
        for r in range(d+1):
            for i in range(degree+1-(d-r)):
                row[i+d-r]+=comb(d,r)*(-p)**(d-r)*raw[r][i]
        need(all(v==0 for v in row[d//2+1:]),'central-moment degree bound')
        moments.append(row[:d//2+1])
    # Independent cumulant-polynomial recurrence p(1-p) d/dp.
    cumulant=[F(0),F(1)]
    cumulants=[F(0),p]
    for d in range(2,degree+1):
        derivative=[(i+1)*cumulant[i+1] for i in range(len(cumulant)-1)]
        cumulant=mul(derivative,[F(0),F(1),F(-1)],d)
        cumulants.append(sum(value*p**i for i,value in enumerate(cumulant)))
    for d in range(2,degree+1):
        expected=[F(0)]*(d//2+1)
        for j in range(2,d+1):
            for i,value in enumerate(moments[d-j]):
                expected[i+1]+=comb(d-1,j-1)*cumulants[j]*value
        need(expected==moments[d],'factorial-moment/cumulant agreement')
    return moments


def compute(order):
    need(type(order) is int and order>=1,'order must be a positive integer')
    V,w=[1],[F(1)]
    for n in range(1,order+2):
        V.append((4*n-2)*V[-1]+sum(V[j]*V[n-1-j] for j in range(n)))
        w.append(w[-1]*F((4*n-3)*(4*n-1),4*n))
    D=[[F(1)]+[F(0)]*order]
    for l in range(1,order+1):
        i=l-1
        row=mul(D[-1],[F(1),F(-i)],order)
        for a in (F(1,4)+i,F(3,4)+i):
            row=mul(row,[a**j for j in range(order+1)],order)
        D.append(row)
    nu=[F(1)]
    for n in range(1,order+1):
        value=F(0)
        for l in range(1,n+1):
            row=mul(mul(D[l],[F(1),F(-l)],order),shifted(nu,l,order),order)
            value+=w[l]/4**l*row[n-l]
        value+=sum(F(V[j],4**(j+1))*D[j][n-j-1] for j in range(1,n))
        nu.append(-value)
    B=bernoulli(order+2)
    def bp(d,x):
        return sum(comb(d,j)*B[j]*x**(d-j) for j in range(d+1))
    logh=[F(0)]
    for r in range(1,order+1):
        logh.append((-1)**(r+1)*(bp(r+1,F(1,4))+bp(r+1,F(3,4))-bp(r+1,F(1,2))-bp(r+1,F(1)))/(r*(r+1)))
    h=mul(nu,exp_series(logh,order),order)
    # Distinct route: V_n/(constant*4^n*n!) in its symmetric endpoint recurrence.
    T=[F(1)]
    for r in range(1,order+1):
        d=r+1
        residual=shifted(T,1,d)
        for b in range(1,r+1):
            denominator=[F(1)]+[F(0)]*d
            for j in range(1,b+1):
                denominator=mul(denominator,[F(1),F(-j)],d)
            tail=mul(reciprocal(denominator,d),shifted(T,b+1,d),d)
            residual[d]+=F(V[b],2*4**b)*tail[d-b-1]
        T.append(-residual[d]/r)
    log_inverse_central=[F(0)]*(order+1)
    for r in range(1,order+1,2):
        log_inverse_central[r]=B[r+1]*(2-F(1,2)**r)/(r*(r+1))
    h_other=mul(T,exp_series(log_inverse_central,order),order)
    need(h==h_other,'independent connected-factorial h-series agreement')
    moments=central_moments(2*order)
    f=[]
    for r in range(order+1):
        total=F(0)
        for j in range(r+1):
            for d in range(2*(r-j)+1):
                power_index=j+d-r
                coefficient=moments[d][power_index] if 0<=power_index<len(moments[d]) else F(0)
                total+=h[j]*F(3,2)**(j+d)*binomial(F(1,2)-j,d)*coefficient
        f.append(total)
    g=[sum(f[a]*f[r+1-a] for a in range(r+2)) for r in range(order)]
    inverse=[]
    for r in range(order):
        # z=x*unit(1/x); only finite rational series are formed.
        unit=[F(1)]+inverse+[F(0)]
        inv=reciprocal(unit,r)
        residual=g[0] if r==0 else F(0)
        for j in range(1,r+1):
            residual+=g[j]*power(inv,j,r)[r-j]
        inverse.append(-residual)
    degree=order-1
    unit=[F(1)]+inverse
    inv=reciprocal(unit,degree)
    residual=inverse[:]
    residual[0]+=g[0]
    for j in range(1,order):
        tail=power(inv,j,degree)
        for r in range(j,order):
            residual[r]+=g[j]*tail[r-j]
    need(all(v==0 for v in residual),'inverse composition residual')
    return {'order':order,'nu':[str(v) for v in nu],
            'gamma_log_h':[str(v) for v in logh],
            'V_factorial':[str(v) for v in T],'h':[str(v) for v in h],
            'profile':[str(v) for v in f],'squared_profile':[str(v) for v in g],
            'inverse':[str(v) for v in inverse],
            'central_moments':[[str(v) for v in row] for row in moments],
            'checks':{'independent_h_coefficients':order+1,
                      'central_moment_recurrences':2*order-1,
                      'inverse_zero_coefficients':order},
            'inverse_residual':[str(v) for v in residual]}


def run():
    return compute(8)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=8)
    print(json.dumps(compute(parser.parse_args().order),sort_keys=True,indent=2))
