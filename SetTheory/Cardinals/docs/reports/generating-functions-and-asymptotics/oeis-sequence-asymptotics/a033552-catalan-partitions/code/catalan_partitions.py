"""Asymptotics for OEIS A033552: partitions into Catalan numbers.

No network access. Exact coefficients use integer arithmetic. Analytic evaluations
use mpmath; their reported decimal values are not interval-certified enclosures.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from math import comb
from typing import Sequence
import mpmath as mp


def catalan(k: int) -> int:
    if k < 0:
        raise ValueError('Catalan index must be nonnegative')
    return comb(2*k, k)//(k+1)


def exact_coefficients(nmax: int) -> list[int]:
    """p[0..nmax]; a part of size 1 is included exactly once."""
    if nmax < 0:
        raise ValueError('nmax must be nonnegative')
    p = [0]*(nmax+1)
    p[0] = 1
    k, c = 1, 1
    while c <= nmax:
        for n in range(c, nmax+1):
            p[n] += p[n-c]
        c = c*2*(2*k+1)//(k+2)
        k += 1
    return p


def r(x):
    x = mp.mpf(x)
    return x*mp.log(4)-mp.log(mp.pi)/2+mp.loggamma(x+mp.mpf('.5'))-mp.loggamma(x+2)


def cutoff_index(u):
    alpha = mp.log(4)
    x = max(mp.mpf(2), (u+mp.mpf('1.5')*mp.log(max(u/alpha, 2))+mp.log(mp.pi)/2)/alpha)
    return mp.findroot(lambda v: r(v)-u, (x, x+1))


@lru_cache(None)
def eulerian_row(n: int) -> tuple[int, ...]:
    """A_n(q) with sum_{l>=1} l^n q^l = q A_n(q)/(1-q)^(n+1)."""
    if n <= 1:
        return (1,)
    prev = eulerian_row(n-1)
    return tuple((k+1)*(prev[k] if k<len(prev) else 0)
                 +(n-k)*(prev[k-1] if k else 0) for k in range(n))


def log_product_and_scaled_cumulants(u, order: int = 6):
    """Return H(t) and B_j=t^j K_j(t), where t=exp(-u)."""
    if order < 1:
        raise ValueError('order must be positive')
    u = mp.mpf(u)
    t = mp.exp(-u)
    cutoff = (mp.mp.dps+15)*mp.log(10)+4*order*mp.log(mp.mp.dps+15)
    H = mp.mpf(0)
    B = [mp.mpf(0) for _ in range(order+1)]
    k, c = 1, 1
    while True:
        y = t*c
        if y > cutoff:
            break
        q = mp.exp(-y)
        den = -mp.expm1(-y)
        H -= mp.log(den)
        for j in range(1, order+1):
            poly = mp.polyval(tuple(reversed(eulerian_row(j-1))), q)
            B[j] += (y/den)**j*q*poly
        c = c*2*(2*k+1)//(k+2)
        k += 1
    return H, B


@dataclass
class SaddleResult:
    n: object
    u: object
    m: object
    log_p0: object
    e1: object
    e2: object
    scaled_cumulants: Sequence

    def log_approximation(self, order: int = 2):
        if order not in (0, 1, 2):
            raise ValueError('implemented numerical orders are 0, 1, 2')
        correction = 1+(self.e1 if order >= 1 else 0)+(self.e2 if order >= 2 else 0)
        if correction <= 0:
            raise ValueError('asymptotic correction is nonpositive at this argument')
        return self.log_p0+mp.log(correction)


def saddle(n) -> SaddleResult:
    n = mp.mpf(n)
    if n <= 1:
        raise ValueError('saddle evaluation requires n > 1')
    logn = mp.log(n)
    u = logn-mp.log(max(mp.mpf(1), logn/mp.log(4)))
    for _ in range(30):
        _, B = log_product_and_scaled_cumulants(u, 2)
        step = (u+mp.log(B[1])-logn)*B[1]/B[2]
        u -= step
        if abs(step) < mp.eps**mp.mpf('.7'):
            break
    else:
        raise ArithmeticError('saddle Newton iteration failed to converge')
    H, B = log_product_and_scaled_cumulants(u, 6)
    logp0 = H+B[1]-u-mp.log(2*mp.pi*B[2])/2
    e1 = B[4]/(8*B[2]**2)-5*B[3]**2/(24*B[2]**3)
    e2 = (-B[6]/(48*B[2]**3)+7*B[3]*B[5]/(48*B[2]**4)
          +35*B[4]**2/(384*B[2]**4)-35*B[3]**2*B[4]/(64*B[2]**5)
          +385*B[3]**4/(1152*B[2]**6))
    return SaddleResult(n, u, cutoff_index(u), logp0, e1, e2, B)


@lru_cache(None)
def fourier_data(dps: int, modes: int):
    with mp.workdps(dps+15):
        alpha = mp.log(4)
        kappa = mp.pi**2/12-mp.euler**2/2-mp.stieltjes(1)
        coeffs, derivs = [], []
        for k in range(1, modes+1):
            s = 2*mp.pi*1j*k/alpha
            gam = mp.gamma(s)
            # At even k, 2**(1-(1+s)) = 1. Avoid eta-quotient cancellation
            # in implementations of the default Riemann zeta path.
            zet = mp.zeta(1+s, method='euler-maclaurin')
            value = gam*zet/alpha
            deriv = -(gam*zet+s*gam*(mp.digamma(s)*zet+mp.zeta(1+s, derivative=1, method='euler-maclaurin')))/alpha**2
            coeffs.append(value)
            derivs.append(deriv)
        return (+kappa, tuple(coeffs), tuple(derivs))


def phase(theta, modes: int | None = None):
    """Return Psi, d_theta Psi, d_theta^2 Psi, partial_alpha Psi at alpha=log 4."""
    if modes is None:
        modes = max(12, int(mp.mp.dps*mp.log(10)*mp.log(4)/mp.pi**2)+4)
    alpha = mp.log(4)
    kappa, coeffs, derivs = fourier_data(mp.mp.dps, modes)
    theta = mp.mpf(theta) % 1
    psi = alpha/12+kappa/alpha
    p1 = mp.mpf(0)
    p2 = mp.mpf(0)
    pa = mp.mpf(1)/12-kappa/alpha**2
    for k, (ck, dk) in enumerate(zip(coeffs, derivs), 1):
        omega = 2*mp.pi*1j*k
        z = mp.exp(omega*theta)
        psi += 2*mp.re(ck*z)
        p1 += 2*mp.re(omega*ck*z)
        p2 += 2*mp.re(omega**2*ck*z)
        pa += 2*mp.re(dk*z)
    return psi, p1, p2, pa


def phase_lattice(theta):
    """Independent real-lattice evaluation of Psi and partial_alpha Psi."""
    theta = mp.mpf(theta) % 1
    alpha = mp.log(4)
    psi = alpha*theta*(1-theta)/2
    pa = theta*(1-theta)/2
    left = int((mp.mp.dps+10)*mp.log(10)/alpha)+2
    for j in range(-left, 9):
        d = j-theta
        v = alpha*d
        y = mp.exp(v)
        if v < 0:
            g = -mp.log((-mp.expm1(-y))/y)
            gp = 1-y/mp.expm1(y)
        else:
            g = -mp.log1p(-mp.exp(-y))
            gp = -y/mp.expm1(y)
        psi += g
        pa += d*gp
    return psi, pa


def constants():
    alpha = mp.log(4)
    A = (1+3*alpha)/2
    eta = mp.mpf(23)/8
    C = mp.log(2)/4+3*mp.log(mp.pi)/4+mp.log(mp.barnesg(mp.mpf('1.5')))
    return alpha, A, eta, C


def core_mu(n):
    n = mp.mpf(n)
    alpha = mp.log(4)
    if n <= 2:
        raise ValueError('large-branch core requires n > 2')
    return -mp.lambertw(-2*alpha/(mp.pi*n*n), -1).real/(2*alpha)


def explicit_log_approximation(n, order: int = 1):
    if order not in (0, 1):
        raise ValueError('explicit numerical orders are 0 and 1')
    alpha, A, eta, C = constants()
    mu = core_mu(n)
    psi, p1, p2, pa = phase(mu)
    ans = alpha*mu**2/2-A*mu+eta*mp.log(mu)+C+psi
    if order:
        D = mp.mpf(1)/6-1/(2*alpha)-mp.mpf('1.5')*pa+17*p1/(8*alpha)-(p1*p1+p2)/(2*alpha**2)
        ans += D/mu
    return ans


def inverse_log_approximation(log_y, order: int = 1):
    """Approximate log(min{n:p(n)>=y}); input is log(y), not y."""
    if order not in (0, 1):
        raise ValueError('inverse numerical orders are 0 and 1')
    Y = mp.mpf(log_y)
    if Y <= 0:
        raise ValueError('log_y must be positive')
    alpha, A, eta, C = constants()
    R = mp.sqrt(2*alpha*Y)
    s = R/alpha
    ans = R+A-mp.log(s)/2-mp.log(mp.pi)/2
    if order:
        psi = phase(s+A/alpha)[0]
        ans += ((A*A-A)/2-alpha*eta*mp.log(s)-alpha*(C+psi))/R
    return ans
