"""Centered Rogers--Dougall subtraction and spectral Taylor coefficients.

All jets are ORDINARY Taylor coefficients, not derivatives. Numeric summation
uses a finite asymptotic tail and is a diagnostic, not a rigorous enclosure.
Gamma denominator zeros are handled by reciprocal-gamma shift polynomials.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
import mpmath as mp


def conv(a: Sequence, b: Sequence, m: int) -> list:
    return [sum(a[k] * b[j-k] for k in range(max(0,j-len(b)+1), min(j,len(a)-1)+1))
            for j in range(m+1)]


def expjet(logjet: Sequence, m: int) -> list:
    out = [mp.exp(logjet[0])] + [mp.mpf(0)]*m
    for j in range(1,m+1):
        out[j] = sum(k*logjet[k]*out[j-k] for k in range(1,j+1))/j
    return out


def zerojet(m: int) -> list:
    return [mp.mpf(0)]*(m+1)


def shift_polynomial(w, m: int) -> tuple[int,list]:
    """prod_{r=0}^{L-1}(w+r+t) with Re(w+L)>0, real w required."""
    if mp.im(w):
        raise ValueError('This diagnostic implementation uses real expansion centers.')
    L = max(0, int(mp.floor(-w))+1)
    out = [mp.mpf(1)] + [mp.mpf(0)]*m
    for r in range(L):
        out = conv(out, [w+r,mp.mpf(1)], m)
    return L,out


@dataclass(frozen=True)
class Params:
    kappa: object
    b: object
    c: object

    def __post_init__(self):
        if min(self.kappa,self.b,self.c,self.d0) <= 0:
            raise ValueError('Require kappa,b,c,d0=1+2*kappa-b-c positive.')

    @property
    def d0(self):
        return 1+2*self.kappa-self.b-self.c

    @classmethod
    def parse(cls,kappa: str,b: str,c: str) -> 'Params':
        def number(s):
            if '/' in s:
                n,d=s.split('/')
                return mp.mpf(n)/mp.mpf(d)
            return mp.mpf(s)
        return cls(number(kappa),number(b),number(c))


def a_jets(p: Params,u0,J: int,m: int) -> list[list]:
    """A_j(u0+t), 0<=j<=J, truncated through t^m."""
    rs=[p.kappa,p.b-p.kappa,p.c-p.kappa,p.d0-u0-p.kappa]
    ell=[zerojet(m)]
    for j in range(1,J+1):
        deg=2*j+1
        v=zerojet(m)
        v[0]=-sum(mp.bernpoly(deg,r) for r in rs)/(j*deg)
        for k in range(1,min(m,deg)+1):
            v[k]=-(-1)**k*mp.binomial(deg,k)*mp.bernpoly(deg-k,rs[3])/(j*deg)
        ell.append(v)
    A=[[mp.mpf(1)]+[mp.mpf(0)]*m]
    for j in range(1,J+1):
        v=zerojet(m)
        for k in range(1,j+1):
            z=conv(ell[k],A[j-k],m)
            for r in range(m+1): v[r]+=k*z[r]/j
        A.append(v)
    return A


def w_jet(p: Params,n: int,u0,m: int) -> list:
    """Safe W_n(u0+t), including any denominator Gamma zero."""
    v=n+p.d0-u0
    w=n+p.b+p.c+u0
    if v <= 0:
        raise ValueError('Expansion requires u0 < d0.')
    L,pol=shift_polynomial(w,m)
    logjet=[mp.mpf(0)]+[
        ((-1)**r*mp.polygamma(r-1,v)-mp.polygamma(r-1,w+L))/mp.factorial(r)
        for r in range(1,m+1)]
    base=(n+p.kappa)*mp.gamma(n+2*p.kappa)*mp.gamma(n+p.b)*mp.gamma(n+p.c)
    base*=mp.gamma(v)/(mp.gamma(n+1)*mp.gamma(n+1+2*p.kappa-p.b)
                      *mp.gamma(n+1+2*p.kappa-p.c)*mp.gamma(w+L))
    return [base*x for x in conv(expjet(logjet,m),pol,m)]


def power_jet(x,s0,m: int) -> list:
    """Taylor coefficients of x^(-s0-2t)."""
    return [mp.power(x,-s0)*(-2*mp.log(x))**k/mp.factorial(k) for k in range(m+1)]


def zeta_jet(s0,a,m: int) -> list:
    """Taylor coefficients of zeta(s0+2t,a), away from s0=1."""
    if s0 == 1:
        raise ValueError('Use Stieltjes regular part at the pole.')
    return [2**k*mp.zeta(s0,a,derivative=k)/mp.factorial(k) for k in range(m+1)]


def q_jet(p: Params,N: int,m: int) -> list:
    """Analytic Q_N(t)=2t G(-N+t), preserving reciprocal-gamma zeros."""
    Lb,pb=shift_polynomial(p.b-N,m)
    Lc,pc=shift_polynomial(p.c-N,m)
    logjet=[mp.mpf(0)]
    for r in range(1,m+1):
        h=(mp.polygamma(r-1,1)+(-1)**r*mp.polygamma(r-1,p.d0+N)
           -mp.polygamma(r-1,p.b-N+Lb)-mp.polygamma(r-1,p.c-N+Lc)
           +mp.factorial(r-1)*sum(mp.mpf(1)/j**r for j in range(1,N+1)))
        logjet.append(h/mp.factorial(r))
    base=(-1)**N/mp.factorial(N)*mp.gamma(p.b)*mp.gamma(p.c)*mp.gamma(p.d0+N)
    base/=mp.gamma(p.d0)*mp.gamma(p.b-N+Lb)*mp.gamma(p.c-N+Lc)
    pol=conv(pb,pc,m)
    return [base*x for x in conv(expjet(logjet,m),pol,m)]


def closed_resonance_jet(p: Params,N: int,m: int) -> list:
    A=a_jets(p,-N,N,m+1)
    Q=q_jet(p,N,m+1)
    out=[(Q[k+1]-A[N][k+1])/2 for k in range(m+1)]
    reg=[(-2)**k*mp.stieltjes(k,p.kappa)/mp.factorial(k) for k in range(m+1)]
    sub=conv(A[N],reg,m)
    for k in range(m+1): out[k]-=sub[k]
    for j in range(N):
        sub=conv(A[j],zeta_jet(1-2*N+2*j,p.kappa,m),m)
        for k in range(m+1): out[k]-=sub[k]
    return out


def rho(p: Params,N: int):
    return (-1)**N*mp.rf(p.d0,N)*mp.rf(1-p.b,N)*mp.rf(1-p.c,N)/mp.factorial(N)


def collapsed(p: Params,N: int):
    return rho(p,N)/2*(mp.digamma(N+1)-mp.digamma(p.d0+N)-mp.digamma(p.b)
                       -mp.digamma(p.c)+2*mp.digamma(p.kappa))


def gamma_side(p: Params,u):
    return (mp.gamma(u)*mp.gamma(p.b)*mp.gamma(p.c)*mp.gamma(p.d0-u)
            *mp.rgamma(p.b+u)*mp.rgamma(p.c+u)/(2*mp.gamma(p.d0)))


def half_closed(p: Params,N: int):
    u=-N-mp.mpf('0.5')
    A=a_jets(p,u,N,0)
    return gamma_side(p,u)+sum(A[j][0]*mp.bernpoly(2*(N-j)+1,p.kappa)/(2*(N-j)+1)
                               for j in range(N+1))


def series_jet(p: Params,u0,K: int,m: int,M: int=96,J: int=20) -> list:
    """Finite head + asymptotic tail. NOT a certified error enclosure."""
    if K<1 or J<K or M<1 or not -K<u0<p.d0:
        raise ValueError('Require K>=1, J>=K, M>=1, -K<u0<d0.')
    A=a_jets(p,u0,J,m)
    out=zerojet(m)
    for n in range(M):
        w=w_jet(p,n,u0,m)
        for j in range(K):
            z=conv(A[j],power_jet(n+p.kappa,1+2*u0+2*j,m),m)
            for k in range(m+1): w[k]-=z[k]
        for k in range(m+1): out[k]+=w[k]
    for j in range(K,J+1):
        z=conv(A[j],zeta_jet(1+2*u0+2*j,M+p.kappa,m),m)
        for k in range(m+1): out[k]+=z[k]
    return out


def residual_coefficients(p: Params,u0,K: int,z,m: int=0,count: int=240,
                          primitive_order: int=0) -> list:
    A=a_jets(p,u0,K-1,m)
    out=zerojet(m)
    for n in range(count):
        w=w_jet(p,n,u0,m)
        for j in range(K):
            q=conv(A[j],power_jet(n+p.kappa,1+2*u0+2*j,m),m)
            for r in range(m+1): w[r]-=q[r]
        weight=z**n/(n+p.kappa)**primitive_order
        for r in range(m+1): out[r]+=w[r]*weight
    return out


def zeta_primitive(j: int,x):
    H=sum(mp.mpf(1)/r for r in range(1,j+1))
    return (mp.zeta(-j,x,derivative=1)+H*mp.zeta(-j,x))/mp.factorial(j)
