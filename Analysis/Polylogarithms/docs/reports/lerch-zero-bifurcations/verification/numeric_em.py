"""Non-certified mpmath Euler--Maclaurin evaluator, independent of fixed-point code."""
import mpmath as mp
from math import factorial
mp.mp.dps=40

def mul(p,q,n):
    r=[mp.mpf('0')]*(n+1)
    for i, x in enumerate(p[:n+1]):
        for j,y in enumerate(q[:n+1-i]):r[i+j]+=x*y
    return r

def rising(a,r,n):
    p=[mp.mpf(1)]
    for j in range(r):p=mul(p,[mp.mpf(a+j),mp.mpf(1)],n)
    return p

def exp_poly(L,n):return [(-L)**i/mp.factorial(i) for i in range(n+1)]

def F_all(k,a,n=12,N=32,M=16):
    a=mp.mpf(a);p=rising(1,k,n)
    z=[mp.mpf(0)]*(n+1)
    for j in range(N):
        x=a+j;e=exp_poly(mp.log(x),n)
        for i in range(n+1): z[i]+=e[i]/x**(k+1)
    A=a+N;L=mp.log(A);e=exp_poly(L,n)
    # multiply by rising before tail, cancellation on pole
    result=mul(p,z,n)
    # (1+t)_k / (k+t) = (1+t)_{k-1}
    tail=mul(rising(1,k-1,n),e,n)
    for i in range(n+1):result[i]+=A**(-k)*tail[i]
    tail=mul(p,e,n)
    for i in range(n+1):result[i]+=A**(-k-1)*tail[i]/2
    for r in range(1,M+1):
        tail=mul(rising(1,k+2*r-1,n),e,n)
        fac=mp.bernoulli(2*r)/mp.factorial(2*r)*A**(-k-2*r)
        for i in range(n+1):result[i]+=fac*tail[i]
    return [mp.factorial(i)*result[i] for i in range(n+1)]

