"""Exact rational formulas from the companion article.

The mathematical parameter q is an odd prime power. The functions do not
construct a finite field; q=9,25, etc. are valid product-formula evaluations.
Negative residual dimensions have p=mu=0 solely as a summation convention.
All returned probabilities and moments use fractions.Fraction.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod


@lru_cache(None)
def gb(n: int, k: int, q: int) -> int:
    """Gaussian binomial [n choose k]_q, zero outside 0 <= k <= n."""
    if k < 0 or k > n:
        return 0
    value = F(1)
    for i in range(k):
        value *= F(q**(n-i)-1, q**(k-i)-1)
    if value.denominator != 1:
        raise ArithmeticError('Gaussian coefficient unexpectedly nonintegral.')
    return value.numerator


def b(n: int) -> int:
    """Dimension c(n)=n(n+1)/2 of the space of symmetric matrices."""
    return n*(n+1)//2


@lru_cache(None)
def p(n: int, q: int) -> F:
    """Probability that a uniform symmetric n by n matrix is nonsingular."""
    if n < 0:
        return F(0)
    return prod((1-F(1,q**j) for j in range(1,n+1,2)), start=F(1))


@lru_cache(None)
def mu(n: int, q: int) -> F:
    """Mean determinant character, with character zero on singular matrices."""
    if n < 0 or n % 2:
        return F(0)
    eps = -1 if q % 4 == 3 else 1
    return eps**(n//2) * F(1,q**(n//2)) * p(n,q)


@lru_cache(None)
def rho(k: int, a: int, q: int) -> F:
    """Full-row-rank probability for a uniform k by a rectangular matrix."""
    if k > a:
        return F(0)
    return prod((1-F(1,q**j) for j in range(a-k+1,a+1)), start=F(1))


@lru_cache(None)
def moments(r: int, t: int, q: int) -> tuple[F,F,F]:
    """Covariance kernels (K_J,K_D,K_JD) for two r-spaces meeting in t."""
    if not 0 <= t <= r:
        raise ValueError('Require 0 <= t <= r.')
    a = r-t
    eps = -1 if q % 4 == 3 else 1
    JJ = DD = JD = F(0)
    for k in range(min(t,a)+1):
        weight = F(gb(t,k,q),q**(b(t)-b(t-k)))
        A = rho(k,a,q)*p(a-k,q)
        B = eps**k*rho(k,a,q)*mu(a-k,q)
        JJ += weight*p(t-k,q)*A*A
        DD += weight*p(t-k,q)*B*B
        JD += weight*mu(t-k,q)*A*B
    return JJ-p(r,q)**2, DD-mu(r,q)**2, JD-p(r,q)*mu(r,q)


def variances(r: int, q: int) -> tuple[list[F],list[F],list[F]]:
    """Return (whole-family, contrast, one-leg) moment triples (J,D,JD)."""
    if r < 1:
        raise ValueError('Generator dimension must be positive.')
    N = 2*prod(q**j+1 for j in range(1,r))
    avg, delta, same = [F(0)]*3, [F(0)]*3, [F(0)]*3
    for t in range(r+1):
        w = F(gb(r,t,q)*q**((r-t)*(r-t-1)//2),N)
        kernels = moments(r,t,q)
        for j in range(3):
            avg[j] += w*kernels[j]
            delta[j] += 4*(-1)**(r-t)*w*kernels[j]
            if (r-t) % 2 == 0:
                same[j] += 2*w*kernels[j]
    return avg,delta,same


def grassmann_variances(n: int, r: int, q: int) -> list[F]:
    """Moment triple for all r-subspaces of an n-space, with n >= 2r."""
    if not n >= 2*r >= 2:
        raise ValueError('Require n >= 2r >= 2.')
    result = [F(0)]*3
    for t in range(r+1):
        w = F(gb(r,t,q)*gb(n-r,r-t,q)*q**((r-t)**2),gb(n,r,q))
        for j,kernel in enumerate(moments(r,t,q)):
            result[j] += w*kernel
    return result


def common_moments(r: int, q: int) -> tuple[F,F,F]:
    """Return E[C], E[C(C-1)], E[Z^2] for common-generator counts."""
    N = 2*prod(q**j+1 for j in range(1,r))
    lam = F(N,q**b(r))
    R = sum((F(gb(r,a,q),q**(a*(r+1-a))) for a in range(1,r+1)),F(0))
    return lam,lam*R,lam*p(r,q)
