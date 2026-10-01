from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path


def mul(a,b,n):
    out=[F(0)]*(n+1)
    for i,x in enumerate(a[:n+1]):
        for j,y in enumerate(b[:n+1-i]): out[i+j]+=x*y
    return out


def power(a,m,n):
    out=[F(1)]+[F(0)]*n
    while m:
        if m&1: out=mul(out,a,n)
        a=mul(a,a,n);m//=2
    return out


def inverse(a,n):
    if a[0]!=1: raise ValueError('Unit series needed')
    out=[F(1)]+[F(0)]*n
    for j in range(1,n+1): out[j]=-sum(a[i]*out[j-i] for i in range(1,j+1))
    return out


def source_integer(d,k,q):
    R=2*d+q+1
    falling=[F(1)]+[F(0)]*d
    for j in range(R): falling=mul(falling,[F(2*d-j),F(1)],d)
    g0=[F(1)]+[F(0)]*d
    if k==0: return mul(falling,g0,d)[d]
    c=[F(2*d-q),F(2)]+[F(0)]*max(0,d-1)
    g1=c[:d+1]
    for j in range(1,k):
        g2=mul(c,g1,d)
        g2=[x+j*(j+R)*y for x,y in zip(g2,g0)]
        g0,g1=g1,g2
    return mul(falling,g1,d)[d]


def hyperbolic_coefficient(d,k,q):
    R=2*d+q+1;M=k+R;b=q-2*d;n=M-d
    sinh_over_x=[F(1,factorial(j+1)) if j%2==0 else F(0) for j in range(n+1)]
    cosh=[F(1,factorial(j)) if j%2==0 else F(0) for j in range(n+1)]
    exponential=[F((-b)**j,factorial(j)) for j in range(n+1)]
    a=power(inverse(sinh_over_x,n),M+1,n)
    a=mul(a,power(cosh,k,n),n)
    a=mul(a,exponential,n)
    return F(factorial(M),factorial(d))*F(1,2**(R-d))*a[n]


rows=[]
for d in range(1,5):
    for k in range(4):
        for q in range(7):
            old=source_integer(d,k,q)
            new=hyperbolic_coefficient(d,k,q)
            if old!=new: raise RuntimeError((d,k,q,old,new))
            if new.denominator!=1: raise RuntimeError('Unexpected noninteger')
            rows.append({'d':d,'k':k,'q':q,'H':new.numerator})
Path(__file__).with_name('reduction_checks.json').write_text(json.dumps({'cases':len(rows),'status':'PASS','rows':rows},indent=2)+'\n')
print(f'{len(rows)} independent exact coefficient checks passed')
