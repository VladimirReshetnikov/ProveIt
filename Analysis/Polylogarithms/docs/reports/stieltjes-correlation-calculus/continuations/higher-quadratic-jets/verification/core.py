"""Reproducible formulas for Higher Quadratic Spectral Jets.

All floating-point routines are diagnostics, not interval certificates.
Polynomial coefficient lists are in increasing degree. Exact coefficients
are built with Fraction, independently of SymPy's rising factorials.
"""
from __future__ import annotations
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, comb, ceil
from typing import Sequence
import mpmath as mp


def mul_linear(poly: Sequence[Q], c: Q) -> list[Q]:
    out = list(poly) + [Q(0)]
    for i, x in enumerate(poly):
        out[i + 1] += c * x
    return out


@lru_cache(None)
def c_coeff(j: int) -> tuple[Q, ...]:
    """Coefficients of (2s)_(2j)/(2j)! - (s)_j/j!."""
    if j < 1:
        raise ValueError("j must be positive")
    left, right = [Q(1)], [Q(1)]
    for h in range(1, 2*j):
        left = mul_linear(left, Q(2, h))
    for h in range(1, j):
        right = mul_linear(right, Q(1, h))
    return tuple([Q(0)] + [(left[k] - (right[k] if k < len(right) else 0))/j
                            for k in range(len(left))])


@lru_cache(None)
def rising_coeff(j: int) -> tuple[Q, ...]:
    """Coefficients of (s)_j/j!."""
    if j == 0:
        return (Q(1),)
    p = [Q(1)]
    for h in range(1, j):
        p = mul_linear(p, Q(1, h))
    return tuple([Q(0)] + [v/j for v in p])


def to_mp(q):
    return mp.mpf(q.numerator)/q.denominator if isinstance(q, Q) else mp.mpf(q)


def peval(poly, x):
    out = 0*x
    for c in reversed(poly):
        out = out*x + to_mp(c)
    return out


def _add(p, q):
    return [(p[j] if j < len(p) else Q(0)) +
            (q[j] if j < len(q) else Q(0)) for j in range(max(len(p),len(q)))]


@lru_cache(None)
def pab(m: int):
    """Exact half-integer Bessel polynomials P_m,A_m,B_m."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    P = tuple(Q(factorial(m+j),factorial(j)*factorial(m-j)*2**j) for j in range(m+1))
    A = tuple((-1)**(m+j)*v for j,v in enumerate(P))
    if m == 0:
        B = (Q(0),)
    elif m == 1:
        B = (Q(0), Q(2))
    else:
        pm,bprev,bprev2 = pab(m-1)[0],pab(m-1)[2],pab(m-2)[2]
        B = tuple(_add(bprev2, [Q(0)]+_add([(2*m-1)*v for v in bprev], [2*v for v in pm])))
    return P,A,B


def zjet(q, a, r: int):
    return mp.zeta(q,a) if r == 0 else mp.diff(lambda s:mp.zeta(s,a),q,r)


def _tail_terms(ratio):
    if not 0 <= ratio < 1:
        raise ValueError("tail ratio must be in [0,1)")
    if ratio == 0:
        return 4
    return max(12, int(mp.ceil((mp.mp.dps+15)*mp.log(10)/(-mp.log(ratio))))+6)


def delta_jet(a, b, weights, r: int, head: int | None = None):
    """Global harmonic/Stieltjes formula for Delta_r(W)."""
    a,b=mp.mpf(a),mp.mpf(b)
    if a<=0 or b<=0 or r<1:
        raise ValueError("a,b>0 and integer r>=1 required")
    head=max(0,int(mp.ceil(2*b-a))+1) if head is None else head
    A=a+head
    if A<=b:
        raise ValueError("the retained tail must start above b")
    total=mp.mpc(0)
    for n in range(head):
        x=a+n
        total+=peval(weights,x)*(2**(r-1)*((-mp.log(x+1j*b))**r+(-mp.log(x-1j*b))**r)
                                   -(-mp.log(x*x+b*b))**r)
    J=_tail_terms((b/A)**2)
    for j in range(1,J+1):
        c=c_coeff(j)
        at=lambda k:to_mp(c[k]) if k<len(c) else mp.mpf(0)
        for d,w in enumerate(weights):
            if not w:
                continue
            q=2*j-d
            v=mp.mpf(0)
            if q==1:
                v=at(r+1)/2
                for k in range(2,r+1):
                    v+=at(k)*(-2)**(r-k)*mp.stieltjes(r-k,A)/mp.factorial(r-k)
            else:
                for k in range(2,r+1):
                    if at(k):
                        v+=at(k)*2**(r-k)*zjet(q,A,r-k)/mp.factorial(r-k)
            total+=mp.factorial(r)*to_mp(w)*(-1)**j*b**(2*j)*v
    return total


def separate_delta_jet(a,b,d:int,r:int):
    """Independent route: complex-shift Hurwitz jets minus quadratic jets.
    Uses b<a and separately expands (s)_j, not the cancellation polynomial C_j.
    """
    a,b=mp.mpf(a),mp.mpf(b)
    if not 0<b<a:
        raise ValueError("this independent check requires 0<b<a")
    F=mp.mpc(0)
    for sign in (1,-1):
        shift=sign*1j*b
        F+=mp.fsum(comb(d,k)*(-shift)**(d-k)*zjet(-k,a+shift,r) for k in range(d+1))
    Z=2**r*zjet(-d,a,r)
    for j in range(1,_tail_terms((b/a)**2)+1):
        p=rising_coeff(j)
        at=lambda k:to_mp(p[k]) if k<len(p) else mp.mpf(0)
        q=2*j-d
        v=mp.mpf(0)
        if q==1:
            v=at(r+1)/2
            for k in range(1,r+1):
                v+=at(k)*(-2)**(r-k)*mp.stieltjes(r-k,a)/mp.factorial(r-k)
        else:
            for k in range(1,r+1):
                if at(k):
                    v+=at(k)*2**(r-k)*zjet(q,a,r-k)/mp.factorial(r-k)
        Z+=mp.factorial(r)*(-1)**j*b**(2*j)*v
    return 2**(r-1)*F-Z


def arctan_square(a,b):
    return -mp.re(delta_jet(a,b,[1],2))/4


def j_integral(p,a,b):
    """Ordinary complex polylogarithm integral J_p."""
    def integrand(w):
        exponent=-2*mp.pi*b*w+2j*mp.pi*a
        # Avoid log(1-z) at quadrature nodes with astronomically tiny z.
        # The convergent defining series is stable in this region.
        z=mp.exp(exponent)
        if mp.re(exponent)<-(mp.mp.dps+15)*mp.log(10)-max(0,-mp.re(p)):
            return z/(w+1)  # omitted terms are quadratically smaller
        return mp.polylog(p,z)/(w+1)
    return mp.quad(integrand,[1,2,4,mp.inf])


def j_series(p,a,b):
    N=int(mp.ceil((mp.mp.dps+18)*mp.log(10)/(2*mp.pi*b)))+8
    return mp.fsum(mp.exp(2j*mp.pi*a*n+2*mp.pi*b*n)*mp.e1(4*mp.pi*b*n)/n**p
                   for n in range(1,N+1))


def second_fourier(m:int,a,b):
    """Second jet E''(-m), finite polylog/J reduction evaluated spectrally."""
    a,b=mp.mpf(a),mp.mpf(b)
    P,A,B=pab(m)
    N=int(mp.ceil((mp.mp.dps+18)*mp.log(10)/(2*mp.pi*b)))+12
    cm=mp.euler-mp.harmonic(m)+mp.log(mp.pi/b)
    acc=mp.mpf(0)
    for n in range(1,N+1):
        u=2*mp.pi*b*n
        poly=peval(P,1/u)*(cm+mp.log(n))-peval(B,1/u)-peval(A,1/u)*mp.exp(2*u)*mp.e1(2*u)
        acc+=mp.cos(2*mp.pi*a*n)*mp.exp(-u)*poly/n**(m+1)
    lm0=-2**(2*m+1)*mp.factorial(m)**2*mp.pi*b**(2*m+1)/mp.factorial(2*m+1)
    return 4*lm0*(mp.harmonic(2*m+1)-mp.harmonic(m)-mp.log(2*b)) \
           +4*(-1)**m*mp.factorial(m)*b**m/mp.pi**m*acc


def second_binomial(m:int,a,b):
    """Independent second jet from the quadratic binomial/Hurwitz expansion."""
    a,b=mp.mpf(a),mp.mpf(b)
    gap=min(a,1-a)
    if not 0<b<gap:
        raise ValueError("requires 0<b<min(a,1-a)")
    def R(q,r):
        return zjet(q,a,r)+zjet(q,1-a,r)
    out=mp.mpf(0)
    for j in range(_tail_terms((b/gap)**2)+m+1):
        q=2*j-2*m
        if j<=m:
            h=mp.fsum(mp.mpf(1)/k for k in range(m-j+1,m+1))
            h2=mp.fsum(mp.mpf(1)/k**2 for k in range(m-j+1,m+1))
            out+=comb(m,j)*b**(2*j)*((h*h-h2)*R(q,0)-4*h*R(q,1)+4*R(q,2))
        else:
            factor=(-1)**(j+m)*b**(2*j)/(j*comb(j-1,m))
            out+=factor*(2*(mp.harmonic(j-m-1)-mp.harmonic(m))*R(q,0)+4*R(q,1))
    return out


def e1_resolvent(a,u):
    b=mp.sqrt(u)
    return mp.pi/b*mp.sinh(2*mp.pi*b)/(mp.cosh(2*mp.pi*b)-mp.cos(2*mp.pi*a))


def e_integer(N:int,a,u):
    """Positive integer resolvent: direct finite head plus Hurwitz tail."""
    b=mp.sqrt(u);head=max(1,int(mp.ceil(2*b))+1)
    A,B=a+head,1-a+head
    out=mp.fsum(((n+a)**2+u)**(-N)+((n+1-a)**2+u)**(-N) for n in range(head))
    for j in range(_tail_terms(u/min(A,B)**2)+1):
        out+=(-1)**j*mp.rf(N,j)/mp.factorial(j)*u**j*(mp.zeta(2*N+2*j,A)+mp.zeta(2*N+2*j,B))
    return out


def T(l:int,u,v):
    def diffpow(k):
        return (u-v)*mp.fsum(u**j*v**(k-1-j) for j in range(k))
    return (-1)**l*mp.fsum(diffpow(k)*diffpow(l-k)/(k*(l-k)) for k in range(1,l))


def k_sum(a,u,v,P):
    """Globally convergent polynomial-subtracted logarithmic square."""
    a,u,v=map(mp.mpf,(a,u,v))
    if u==v:
        return mp.mpf(0)
    D=len(P)-1;head=max(1,int(mp.ceil(2*mp.sqrt(max(u,v))))+1)
    A,B=a+head,1-a+head
    J=_tail_terms(max(u,v)/min(A,B)**2)+D+4
    ts={l:T(l,u,v) for l in range(2,J+1)}
    def sub(y):
        return mp.fsum(to_mp(P[d])*ts[l]*y**(d-l) for d in range(2,D+1) for l in range(2,d+1))
    total=mp.mpf(0)
    for n in range(head):
        for x in (n+a,n+1-a):
            y=x*x
            total+=peval(P,y)*mp.log1p((u-v)/(y+v))**2-sub(y)
    for d,p in enumerate(P):
        if p:
            total+=to_mp(p)*mp.fsum(ts[l]*(mp.zeta(2*(l-d),A)+mp.zeta(2*(l-d),B))
                                      for l in range(max(2,d+1),J+1))
    return total


def k_integral(a,u,v,P):
    a,u,v=map(mp.mpf,(a,u,v))
    if u==v:
        return mp.mpf(0)
    if u<v:
        u,v=v,u
    h=u-v
    return 2*h*mp.quad(lambda t:peval(P,-v-h*t)*e1_resolvent(a,v+h*t)*mp.log((1-t)/t),[0,.5,1])


def p_derivative_at(P,x,l):
    return mp.fsum(to_mp(P[d])*mp.factorial(d)/mp.factorial(d-l)*x**(d-l)
                   for d in range(l,len(P)))


def k_collision_series(a,u,h,P,terms:int=30):
    total=mp.mpf(0)
    for r in range(2,terms+1):
        c=mp.fsum(p_derivative_at(P,-u,l)/mp.factorial(l)*e_integer(r-l,a,u)
                 for l in range(min(len(P)-1,r-1)+1))
        total+=2*(-1)**r*mp.harmonic(r-1)/r*h**r*c
    return total


def product_second_binomial(a,u,v,P):
    """Independent product second jet from a double Pochhammer expansion.

    Requires both squared masses below the squared lattice gap. The double
    sum is collected by total degree, without using the logarithmic defect.
    """
    a,u,v=map(mp.mpf,(a,u,v));gap=min(a,1-a)
    if not 0<max(u,v)<gap**2:
        raise ValueError('requires 0<u,v<min(a,1-a)^2')
    def R(q,k): return zjet(q,a,k)+zjet(q,1-a,k)
    total=mp.fsum(to_mp(p)*16*R(-2*d,2) for d,p in enumerate(P) if p)
    limit=_tail_terms(max(u,v)/gap**2)+len(P)+4
    for l in range(1,limit+1):
        cross=mp.fsum(u**j*v**(l-j)/(j*(l-j)) for j in range(1,l))
        for d,p in enumerate(P):
            if p:
                q=2*l-2*d
                total+=to_mp(p)*(-1)**l*((u**l+v**l)*(2*mp.harmonic(l-1)*R(q,0)/l+8*R(q,1)/l)+2*cross*R(q,0))
    return total
