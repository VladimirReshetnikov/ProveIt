#!/usr/bin/env python3
"""Catalan-partition statistics; exact integer combinatorics and mpmath analysis.
No network access is required. Floating point values are not interval certificates.
"""
from __future__ import annotations
from math import comb, factorial
from functools import lru_cache
import mpmath as mp


def catalans(count: int) -> list[int]:
    if count < 1:
        raise ValueError('count must be positive')
    return [comb(2*k,k)//(k+1) for k in range(1,count+1)]


def parts_to(n: int) -> list[int]:
    out=[]; k=1; c=1
    while c <= n:
        out.append(c); c=c*2*(2*k+1)//(k+2); k+=1
    return out


def exact_statistics(nmax: int, checkpoints: list[int]):
    """Counts and first two raw length sums, with prefix statistics at checkpoints."""
    if nmax < 1 or any(n<0 or n>nmax for n in checkpoints):
        raise ValueError('invalid bounds')
    p=[0]*(nmax+1); u=[0]*(nmax+1); v=[0]*(nmax+1); p[0]=1
    prefix={n:{} for n in checkpoints}
    for k,c in enumerate(parts_to(nmax),1):
        for n in range(c,nmax+1):
            j=n-c
            p[n]+=p[j]
            u[n]+=u[j]+p[j]
            v[n]+=v[j]+2*u[j]+p[j]
        for n in checkpoints:
            prefix[n][k]=(p[n],u[n],v[n])
    return p,u,v,prefix


def log_catalan(x):
    return x*mp.log(4)-mp.log(mp.pi)/2+mp.loggamma(x+mp.mpf('.5'))-mp.loggamma(x+2)


def scaled_cumulants(t, order: int = 8):
    out=[mp.mpf(0)]*(order+1)
    k=1; c=1
    cutoff=(mp.mp.dps+20)*mp.log(10)
    while True:
        z=t*c
        if z > cutoff+order*mp.log(cutoff+2):
            break
        q=mp.exp(-z)
        for r in range(1,order+1):
            out[r]+=z**r*mp.polylog(1-r,q)
        c=c*2*(2*k+1)//(k+2); k+=1
    return out


def saddle(n: int, order: int = 8):
    if n <= 0:
        raise ValueError('n must be positive')
    guess=mp.log(n+2)/(mp.log(4)*n)
    # A bracketed solve in log t avoids invalid negative iterates.
    def f(u):
        t=mp.exp(u)
        return scaled_cumulants(t,1)[1]/t-n
    lo=mp.log(guess)-3; hi=mp.log(guess)+3
    while f(lo)<0: lo-=3
    while f(hi)>0: hi+=3
    for _ in range(4*mp.mp.dps):
        mid=(lo+hi)/2
        if f(mid)>0: lo=mid
        else: hi=mid
    t=mp.exp((lo+hi)/2)
    m=mp.findroot(lambda x:log_catalan(x)+mp.log(t),
                  (mp.log(1/t)/mp.log(4)+1,mp.log(1/t)/mp.log(4)+5))
    return t,m,scaled_cumulants(t,order)


def limit_laplace(s, derivative_order: int = 6):
    """Return L(s), and a_l = d^l/dv^l L(s/(1+v)) at v=0."""
    # The omitted reciprocal tail is below the working precision.
    cs=catalans(2*mp.mp.dps+30)
    L=mp.mpf(1)
    ell=[mp.mpf(0)]*(derivative_order+1)
    for ci in cs:
        c=mp.mpf(ci); L*=c/(c+s)
        b=c/(c+s)
        for r in range(1,derivative_order+1):
            ell[r]+=(-1)**(r+1)*(1-b**r)/r
    e=[mp.mpf(1)]+[mp.mpf(0)]*derivative_order
    for k in range(1,derivative_order+1):
        e[k]=mp.fsum(r*ell[r]*e[k-r] for r in range(1,k+1))/k
    return L,[L*factorial(k)*e[k] for k in range(derivative_order+1)]


def odd_double_factorial(n: int) -> int:
    if n <= 0: return 1
    ans=1
    for j in range(1,n+1,2): ans*=j
    return ans


@lru_cache(None)
def operator_terms(J: int):
    """Tuples (l, (k3,...,k_(2J+2)), sign*GaussianMoment, denominator)."""
    if J<0: raise ValueError('order must be nonnegative')
    out=[]
    for l in range(2*J+1):
        def walk(r,left,ks):
            if r>2*J+2:
                R=sum((i+3)*k for i,k in enumerate(ks))
                if (l+R)%2==0:
                    sign=-1 if ((l-R)//2)%2 else 1
                    den=factorial(l)
                    for i,k in enumerate(ks): den*=factorial(k)*factorial(i+3)**k
                    out.append((l,tuple(ks),sign*odd_double_factorial(l+R-1),den))
                return
            for k in range(left//(r-2)+1):
                walk(r+1,left-(r-2)*k,ks+[k])
        walk(3,2*J-l,[])
    return tuple(out)


def saddle_operator(B,a,J):
    ans=mp.mpf(0)
    for l,ks,num,den in operator_terms(J):
        R=sum((i+3)*k for i,k in enumerate(ks))
        term=mp.mpf(num)/den*a[l]/B[2]**((l+R)//2)
        for i,k in enumerate(ks): term*=B[i+3]**k
        ans+=term
    return ans


def conditional_laplace(B,s,J):
    L,a=limit_laplace(s,2*J)
    one=[mp.mpf(1)]+[mp.mpf(0)]*(2*J)
    return saddle_operator(B,a,J)/saddle_operator(B,one,J)


def conditional_moment(B,r,mu,J):
    a=[mu*(-1)**l*mp.rf(r,l) for l in range(2*J+1)]
    one=[mp.mpf(1)]+[mp.mpf(0)]*(2*J)
    return saddle_operator(B,a,J)/saddle_operator(B,one,J)


def phase_extreme(theta,h):
    G=mp.mpf(1); S1=mp.mpf(0); S2=mp.mpf(0); U=mp.mpf(0)
    for j in range(h+1,max(h+2,30)):
        d=j-theta; v=mp.power(4,d)
        if v > (mp.mp.dps+15)*mp.log(10): break
        q=mp.exp(-v)
        G*=1-q
        S1+=v*q/(1-q)
        S2+=v*v*q/(1-q)**2
        U+=d*v*q/(1-q)
    correction=-mp.mpf('1.5')*U+(S2-S1*S1-2*S1)/2
    return G,S1,S2,U,correction


def exact_tail_amplitude(t,K,order=6):
    cs=catalans(max(K+30,2*mp.mp.dps+30))
    G=mp.mpf(1); logder=[mp.mpf(0)]*(order+1)
    for ci in cs[K:]:
        v=t*ci
        if v>(mp.mp.dps+20)*mp.log(10)+order*mp.log(mp.mp.dps+20): break
        q=mp.exp(-v); G*=1-q
        for r in range(1,order+1):
            logder[r]+=(-1)**(r-1)*v**r*mp.polylog(1-r,q)
    # Exponential Bell recurrence for ordinary derivatives.
    a=[G]+[mp.mpf(0)]*order
    for r in range(1,order+1):
        a[r]=mp.fsum(comb(r-1,j-1)*logder[j]*a[r-j] for j in range(1,r+1))
    return G,a


def residues(count=20):
    cs=catalans(max(count+30,2*mp.mp.dps+30)); out=[]
    for j in range(count):
        cj=mp.mpf(cs[j]); a=mp.mpf(1)
        for k,ci in enumerate(cs):
            if k!=j: a*=mp.mpf(ci)/(ci-cj)
        out.append(a)
    return cs[:count],out


def survival(x,cs,ds):
    return mp.fsum(d*mp.exp(-c*x) for c,d in zip(cs,ds))


def quantile_series(epsilon,ds):
    d1,d2,d3=ds[:3]
    e=epsilon
    terms=[mp.log(d1/e), d2/d1**2*e,
           -3*d2**2/(2*d1**4)*e**2,
           10*d2**3/(3*d1**6)*e**3,
           (d3/d1**5-35*d2**4/(4*d1**8))*e**4]
    return [mp.fsum(terms[:k+1]) for k in range(5)]


def weighted_count(n,w):
    p=[0.0]*(n+1);p[0]=1.0
    for c in parts_to(n):
        for j in range(c,n+1): p[j]+=w*p[j-c]
    return p[n]
