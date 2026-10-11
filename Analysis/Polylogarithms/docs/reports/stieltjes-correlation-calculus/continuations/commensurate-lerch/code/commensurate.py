"""Finite pole-lattice calculus for commensurate Lerch convolutions.

Exact coefficients use SymPy. Numerical evaluations use mpmath and the
pole-free formulas proved in the accompanying article. No network access.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import reduce
from math import gcd, lcm
from typing import Iterable
import sympy as sp
import mpmath as mp

@dataclass(frozen=True)
class PoleTable:
    rates: tuple
    period: sp.Rational
    sign: int
    coefficients: dict  # (rho,k) -> coefficient of (p-rho)^(-k)


def rational_rates(rates: Iterable) -> tuple:
    rates = tuple(sp.Rational(q) for q in rates)
    if not rates or any(q <= 0 for q in rates):
        raise ValueError("Supply at least one strictly positive rational rate.")
    return rates


def period_for(rates: Iterable) -> sp.Rational:
    qs = rational_rates(rates)
    return sp.Rational(reduce(lcm, (int(q.p) for q in qs)),
                       reduce(gcd, (int(q.q) for q in qs)))


def log_csc_polynomial(n: int):
    """d^n/dtheta^n log(csc(theta)), as polynomial in cot(theta)."""
    if n < 1:
        raise ValueError("n must be positive")
    t = sp.Symbol('t')
    f = -t
    for _ in range(1, n):
        f = sp.expand(-(1+t*t)*sp.diff(f, t))
    return t, f


def pole_table(rates: Iterable) -> PoleTable:
    """Bell-polynomial local expansion; exact real cyclotomic coefficients."""
    qs = rational_rates(rates)
    Q = period_for(qs)
    sign = (-1)**sum(int(Q/q) for q in qs)
    poles = sorted({q*n for q in qs for n in range(1, int(Q/q)+1)})
    out = {}
    r = len(qs)
    for rho in poles:
        polar = [q for q in qs if (rho/q).q == 1]
        regular = [q for q in qs if (rho/q).q != 1]
        d = len(polar)
        leading = sp.Integer((-1)**sum(int(rho/q) for q in polar))
        for q in regular:
            leading *= 1/(q*sp.sin(sp.pi*rho/q))
        leading = sp.simplify(leading)
        ell = [sp.Integer(0)]
        for n in range(1, d):
            val = sp.Integer(0)
            if n % 2 == 0:
                val += 2*sp.factorial(n-1)*sp.zeta(n)/sp.pi**n*sum(q**(-n) for q in polar)
            t, poly = log_csc_polynomial(n)
            val += sum(poly.subs(t, sp.cot(sp.pi*rho/q))/q**n for q in regular)
            ell.append(sp.simplify(val))
        b = [sp.Integer(1)]
        for n in range(1, d):
            b.append(sp.simplify(sum(ell[j]*b[n-j]/sp.factorial(j-1)
                                     for j in range(1, n+1))/n))
        for k in range(1, d+1):
            out[rho, k] = sp.simplify(sp.pi**(r-k)*leading*b[d-k])
    return PoleTable(qs, Q, sign, out)


def direct_local_table(rates: Iterable) -> PoleTable:
    """Independent truncated reciprocal-sine series (no logarithms/Bell rule)."""
    qs = rational_rates(rates)
    Q = period_for(qs)
    sign = (-1)**sum(int(Q/q) for q in qs)
    poles = sorted({q*n for q in qs for n in range(1, int(Q/q)+1)})
    out = {}
    r = len(qs)
    for rho in poles:
        d = sum((rho/q).q == 1 for q in qs)
        prod = [sp.Integer(1)] + [sp.Integer(0)]*(d-1)
        for q in qs:
            polar = (rho/q).q == 1
            if polar:
                # sin(t/q)/(t/q), with (-1)^(rho/q) outside.
                den = [sp.Integer(0)]*d
                for j in range(0, d, 2):
                    den[j] = sp.Rational((-1)**(j//2), sp.factorial(j+1))/q**j
                scale = sp.Integer((-1)**int(rho/q))
            else:
                den = [sp.sin(sp.pi*rho/q + j*sp.pi/2)/(sp.factorial(j)*q**j)
                       for j in range(d)]
                scale = 1/q
            inv = [1/den[0]]
            for n in range(1, d):
                inv.append(sp.simplify(-sum(den[j]*inv[n-j] for j in range(1,n+1))/den[0]))
            fac = [sp.simplify(scale*x) for x in inv]
            prod = [sp.simplify(sum(prod[j]*fac[n-j] for j in range(n+1))) for n in range(d)]
        for k in range(1, d+1):
            out[rho,k] = sp.simplify(sp.pi**(r-k)*prod[d-k])
    return PoleTable(qs,Q,sign,out)


def mval(x):
    """Convert exact SymPy constants without introducing binary floats."""
    return mp.mpf(str(sp.N(x, mp.mp.dps+12)))


def rising(w, n: int):
    return mp.fprod(w+j for j in range(n))


def eta(s, a):
    if s == 1:
        return (mp.digamma((a+1)/2)-mp.digamma(a/2))/2
    return mp.power(2,-s)*(mp.zeta(s,a/2)-mp.zeta(s,(a+1)/2))


def entire_E(v, a):
    return mp.mpf(1) if v == 0 else v*mp.zeta(v+1,a)


def zeta_difference(s,a,b):
    return mp.digamma(b)-mp.digamma(a) if s == 1 else mp.zeta(s,a)-mp.zeta(s,b)


def central(tab: PoleTable, w, A=0):
    """C_q,A(w;0), retaining every removable resonance."""
    w, A = mp.mpc(w), mp.mpc(A)
    Q = mval(tab.period)
    if mp.re(A) <= -min(mval(q) for q in tab.rates):
        raise ValueError("The stated common-strip domain requires Re(A)>-min(q).")
    total = mp.mpc(0)
    b0 = (A+Q)/Q
    for (rho,k), a_exact in tab.coefficients.items():
        if a_exact == 0:
            continue
        a = mval(a_exact)
        b = (A+mval(rho))/Q
        if tab.sign == -1:
            total += (-1)**k*a/mp.factorial(k-1)*rising(w,k-1)*mp.power(Q,-w-k+1)*eta(w+k-1,b)
        elif k == 1:
            total -= a*mp.power(Q,-w)*zeta_difference(w,b,b0)
        else:
            total += (-1)**k*a/mp.factorial(k-1)*mp.power(Q,-w-k+1)*rising(w,k-2)*entire_E(w+k-2,b)
    return total


def off_centre(tab: PoleTable, w, A, mu):
    """Finite Lerch formula for real mu<0 (no branch boundary needed)."""
    w,A,mu=mp.mpc(w),mp.mpc(A),mp.mpc(mu)
    if mp.re(A)<=-min(mval(q) for q in tab.rates):
        raise ValueError("Require Re(A)>-min(q).")
    if not mp.im(mu)==0 or not mp.re(mu)<0:
        raise ValueError("This numerical routine uses the proved mu<0 series branch.")
    Q=mval(tab.period)
    z=tab.sign*mp.exp(Q*mu)
    total=mp.mpc(0)
    for (rho,k), ae in tab.coefficients.items():
        a=mval(ae)
        b=(A+mval(rho))/Q
        for j in range(k):
            total -= a*mp.exp(mval(rho)*mu)*(-1)**j*mu**(k-1-j)/(mp.factorial(j)*mp.factorial(k-1-j))*rising(w,j)*mp.power(Q,-w-j)*mp.lerchphi(z,w+j,b)
    return total


def contour(rates, w, A=0, mu=0, jet=0, shifts=None, orders=None):
    """Independent bilateral-transform quadrature; jets differentiate total order."""
    qs=[mval(q) for q in rational_rates(rates)]
    w,A,mu=mp.mpc(w),mp.mpc(A),mp.mpc(mu)
    if not isinstance(jet,int) or jet<0:
        raise ValueError("jet must be a nonnegative integer")
    if shifts is not None:
        if orders is None or len(shifts)!=len(qs) or len(orders)!=len(qs):
            raise ValueError("shifts and orders must both match the number of rates")
        shifts=[mp.mpc(a) for a in shifts]; orders=[mp.mpc(s) for s in orders]
    if shifts is None:
        lo=max(mp.mpf(0),-mp.re(A))
    else:
        lo=max([mp.mpf(0)]+[-mp.re(a) for a in shifts])
    hi=min(qs)
    if not lo<hi:
        raise ValueError("No common weighted strip.")
    c=(lo+hi)/2
    def integrand(t):
        p=c+1j*t
        g=mp.fprod((mp.pi/q)/mp.sin(mp.pi*p/q) for q in qs)*mp.exp(p*mu)
        if shifts is None:
            return g*mp.power(p+A,-w)*mp.power(-mp.log(p+A),jet)
        return g*mp.fprod(mp.power(p+a,-s) for a,s in zip(shifts,orders))
    return mp.quad(integrand,[-mp.inf,0,mp.inf])/(2*mp.pi)


def kernel(tab: PoleTable,x):
    """Elementary logistic convolution kernel; x != 0."""
    if x==0:
        return central(tab,0)
    Q=mval(tab.period)
    num=mp.fsum(mval(a)*mp.exp(mval(rho)*x)*x**(k-1)/mp.factorial(k-1)
                for (rho,k),a in tab.coefficients.items())
    return -num/(1-tab.sign*mp.exp(Q*x))


def pair_master(m: int, s, t, A=0):
    if not isinstance(m,int) or m<1:
        raise ValueError("m must be a positive integer")
    s,t=mp.mpc(s),mp.mpc(t)
    return mp.power(m,t)*central(pole_table((1,m)),s+t,A)


def shifted_harmonic(N, sigma, v, a):
    return mp.fsum(sigma**k*mp.power(k+a,-v) for k in range(N))


def remainder_master(m,N,s,t):
    if not isinstance(N,int) or N<0:
        raise ValueError("N must be a nonnegative integer")
    if not isinstance(m,int) or m<1:
        raise ValueError("m must be a positive integer")
    s,t=mp.mpc(s),mp.mpc(t)
    w=s+t
    sigma=(-1)**(m+1)
    correction=mp.pi*mp.fsum((-1)**(r+1)/mp.sin(mp.pi*r/m)*shifted_harmonic(N,sigma,w,mp.mpf(r)/m)
                            for r in range(1,m))
    correction += sigma*w*shifted_harmonic(N,sigma,w+1,mp.mpf(1))
    return pair_master(m,s,t)-mp.power(m,-s-1)*correction


def unequal_coefficients(orders, deltas, N):
    """h_n=[z^n] product (1+delta_j*z)^(-s_j), 0<=n<=N."""
    if not isinstance(N,int) or N<0 or len(orders)!=len(deltas):
        raise ValueError("Require N>=0 and equally many orders and displacements")
    orders=[mp.mpc(s) for s in orders];deltas=[mp.mpc(d) for d in deltas]
    ans=[mp.mpc(1)]+[mp.mpc(0)]*N
    for s,d in zip(orders,deltas):
        fac=[(-d)**n*rising(s,n)/mp.factorial(n) for n in range(N+1)]
        ans=[mp.fsum(ans[j]*fac[n-j] for j in range(n+1)) for n in range(N+1)]
    return ans


def odd_resonance(rates,N):
    """Exact C_q,0(-N;0) in the parity sector len(q)+N odd."""
    qs=rational_rates(rates)
    r=len(qs)
    if (r+N)%2 != 1 or N<0:
        raise ValueError("Require N>=0 and depth+N odd.")
    degree=r-N-1
    if degree<0:
        return sp.Integer(0)
    z=sp.Symbol('z')
    logseries=sum(sum(2*sp.zeta(2*k)/(2*k)*(z/q)**(2*k)
                          for k in range(1,degree//2+1)) for q in qs)
    return sp.simplify(sp.expand(sp.series(sp.exp(logseries),z,0,degree+1).removeO()).coeff(z,degree)/2)

if __name__ == '__main__':
    print(pole_table((1,2,3)))
