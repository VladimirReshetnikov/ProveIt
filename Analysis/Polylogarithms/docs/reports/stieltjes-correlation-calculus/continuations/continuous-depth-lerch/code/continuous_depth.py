"""Continuous-depth Lerch kernels. Numerical evaluation, not interval arithmetic.

All branches and parameter domains are specified in the accompanying article.
Dependencies: mpmath. Set mp.dps before calling these routines.
"""
from __future__ import annotations
from typing import Any
import mpmath as mp

Number = Any


def kernel(rho: Number, x: Number) -> Number:
    """K_rho(x), Re(rho)>0. Complex rho uses a Gamma PRODUCT, not abs(Gamma)**2."""
    rho, x = mp.mpc(rho), mp.mpc(x)
    if mp.re(rho) <= 0:
        raise ValueError("kernel requires Re(rho)>0")
    return mp.exp((rho - 2)*mp.log(2*mp.pi) + x/2
                  + mp.loggamma(rho/2 + 1j*x/(2*mp.pi))
                  + mp.loggamma(rho/2 - 1j*x/(2*mp.pi))
                  - mp.loggamma(rho))


def kernel_dx(rho: Number, x: Number, order: int = 1) -> Number:
    """First two argument derivatives of the Gamma kernel."""
    if order not in (0, 1, 2):
        raise ValueError("implemented derivative orders are 0, 1, 2")
    k = kernel(rho, x)
    if order == 0:
        return k
    z1, z2 = rho/2 + 1j*x/(2*mp.pi), rho/2 - 1j*x/(2*mp.pi)
    l1 = mp.mpf('0.5') + 1j*(mp.digamma(z1)-mp.digamma(z2))/(2*mp.pi)
    if order == 1:
        return k*l1
    l2 = -(mp.polygamma(1,z1)+mp.polygamma(1,z2))/(4*mp.pi**2)
    return k*(l1*l1+l2)


def negative_profile(rho: Number, a: Number, n: int, x: Number) -> Number:
    """F_{rho,a}(-n;x), implemented for n=0,1,2."""
    if n not in (0,1,2):
        raise ValueError("implemented n values are 0, 1, 2")
    return mp.fsum(mp.binomial(n,j)*(a-1)**(n-j)*kernel_dx(rho,x,j)
                   for j in range(n+1))


def contour_profile(rho: Number, a: Number, s: Number, x: Number = 0,
                    *, c: Number | None = None, order_jet: int = 0,
                    depth_jet: int = 0) -> Number:
    """Ordinary Fourier/Barnes contour for F and spectral/depth derivatives.

    Adaptive quadrature uses the full infinite line. Tolerances belong to the
    caller's validation protocol; working precision alone is no error bound.
    """
    rho, a, s, x = map(mp.mpc, (rho,a,s,x))
    if mp.re(rho)<=0 or mp.re(a)<=0:
        raise ValueError("Re(rho)>0 and Re(a)>0 are required")
    lower = max(mp.mpf(0),1-mp.re(a))
    c = (1+lower)/2 if c is None else mp.mpf(c)
    if not lower<c<1:
        raise ValueError("c must satisfy max(0,1-Re(a))<c<1")
    if abs(mp.im(x)) >= mp.pi*mp.re(rho):
        raise ValueError("x must lie in the open analyticity strip")
    if order_jet<0 or depth_jet<0:
        raise ValueError("jet orders must be nonnegative")
    def integrand(t: Number) -> Number:
        p = c+1j*t
        lg = mp.log(mp.pi/mp.sin(mp.pi*p))
        la = mp.log(p+a-1)
        return mp.exp(p*x + rho*lg - s*la)*(-la)**order_jet*lg**depth_jet
    return mp.quad(integrand, [-mp.inf,-2,-1,0,1,2,mp.inf])/(2*mp.pi)


def fractional_profile(rho: Number, a: Number, s: Number, x: Number = 0) -> Number:
    """Independent positive-order real-integral evaluation; requires Re(s)>0."""
    if min(mp.re(rho),mp.re(a),mp.re(s))<=0:
        raise ValueError("positive real parts of rho, a, and s are required")
    n = max(1, int(mp.ceil(3/mp.re(s))))
    q = lambda u: mp.exp(-(a-1)*u)*kernel(rho,x-u)
    low = mp.quad(lambda v: n*v**(n*s-1)*q(v**n), [0,1])
    high = mp.quad(lambda u: u**(s-1)*q(u), [1,4,mp.inf])
    return (low+high)/mp.gamma(s)


def centered_zeta(rho: Number, s: Number) -> Number:
    """Z_rho(s), by its convergent hyperbolic Mellin integral, Re(s)>0."""
    if min(mp.re(rho),mp.re(s))<=0:
        raise ValueError("this representation needs Re(rho), Re(s)>0")
    n = max(1, int(mp.ceil(3/mp.re(s))))
    q = lambda u: mp.exp(-rho*mp.log(2*mp.cosh(u/2)))
    low = mp.quad(lambda v: n*v**(n*s-1)*q(v**n), [0,1])
    high = mp.quad(lambda u: u**(s-1)*q(u), [1,4,mp.inf])
    return (low+high)/mp.gamma(s)


def entire_e(s: Number, a: Number = 1) -> Number:
    """E_a(s)=s*zeta(s+1,a) with its removable value at s=0."""
    return mp.mpf(1) if s == 0 else s*mp.zeta(s+1,a)


def e_jet_at_zero(m: int, a: Number = 1) -> Number:
    if m<0:
        raise ValueError("m must be nonnegative")
    return mp.mpf(1) if m == 0 else (-1)**(m-1)*m*mp.stieltjes(m-1,a)


def harmonic(k: Number, j: int = 1) -> Number:
    """Analytic continuation of H_k^(j), useful for alternating acceleration."""
    if j<1:
        raise ValueError("harmonic order must be positive")
    if j==1:
        return mp.digamma(k+1)+mp.euler
    return mp.zeta(j)-mp.zeta(j,k+1)


def bell(values: list[Number]) -> Number:
    """Complete exponential Bell polynomial by its defining recurrence."""
    b = [mp.mpf(1)]
    for n in range(1,len(values)+1):
        b.append(mp.fsum(mp.binomial(n-1,j-1)*values[j-1]*b[n-j]
                         for j in range(1,n+1)))
    return b[-1]


def harmonic_summand(k: Number, m: int, q: int) -> Number:
    d = [(-1)**(j-1)*mp.factorial(j-1)*(harmonic(k,j)-(2*m+1)/(2*k)**j)
         for j in range(1,q+1)]
    return (-1)**(k-1)*bell(d)/k**(2*m)
