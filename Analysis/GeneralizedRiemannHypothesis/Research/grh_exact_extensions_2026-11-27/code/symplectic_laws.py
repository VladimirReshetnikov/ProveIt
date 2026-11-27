"""Exact laws proved in the accompanying paper; Python 3 standard library only.

All probabilities and finite-precision calculations use Fraction.  n is even,
the visible block is n by n, the ambient symplectic module has rank 2*n,
and q is the cardinality of the residue field.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod


def qpower(q, e):
    return F(q**e) if e >= 0 else F(1, q**(-e))


@lru_cache(None)
def a(q, n):
    return prod((1 - qpower(q, -j) for j in range(1, n + 1)), start=F(1))


@lru_cache(None)
def u(q, n, k):
    """Nullity k probability of an iid n by n matrix over F_q."""
    if not 0 <= k <= n:
        return F(0)
    return qpower(q, -k*k) * a(q, n)**2 / (a(q, k)**2 * a(q, n-k))


@lru_cache(None)
def C(q, n):
    assert n >= 2 and n % 2 == 0
    return prod((1 - qpower(q, -2*j) for j in range(n//2 + 1, n+1)), start=F(1))


@lru_cache(None)
def R(q, n, k):
    if not 0 <= k <= n//2:
        return F(0)
    return prod(((1-qpower(q, 2*i-n))/(1-qpower(q, i-n)) for i in range(k)), start=F(1))


@lru_cache(None)
def transition(q, k, j):
    """Killed nullity transition, including the isotropy cost."""
    return u(q, k, j) * qpower(q, -j*(j-1)//2)


@lru_cache(None)
def survival(q, k, steps):
    if steps == 0:
        return F(1)
    return sum((transition(q, k, j) * survival(q, j, steps-1)
                for j in range(k+1)), start=F(0))


@lru_cache(None)
def survival_infinite(q, k):
    if k <= 1:
        return F(1)
    return (sum((transition(q, k, j)*survival_infinite(q, j)
                 for j in range(k)), start=F(0)) /
            (1-transition(q, k, k)))


def smith_tv(q, n):
    """Exact at every positive precision, including infinite precision."""
    return (u(q, n, 0)+u(q, n, 1)) * (1/C(q, n)-1)


def full_tv(q, n, precision=None):
    assert precision is None or precision >= 1
    z = (lambda k: survival_infinite(q, k)) if precision is None else (
        lambda k: survival(q, k, precision-1))
    return 1-sum((u(q,n,k)*R(q,n,k)*qpower(q,-k*(k-1)//2)*z(k)
                  for k in range(n//2+1)), start=F(0))


def first_precision_gap(q, n):
    return full_tv(q, n, None)-full_tv(q, n, 1)


def smith_type_likelihood(q, n, exponents):
    assert len(exponents) == n
    return R(q, n, sum(x >= 1 for x in exponents))/C(q,n)


def orientation_support(q, n, exponents):
    s = sum(min(x,y) for i,x in enumerate(exponents) for y in exponents[i+1:])
    k = sum(x >= 1 for x in exponents)
    return qpower(q,-s)*R(q,n,k)


def precision_eigenvalue(q, k):
    return qpower(q, -(3*k*k-k)//2)


def limiting_constant_interval(q, precision=None, cutoff=12, product_cutoff=100):
    """Certified interval for lim_even_n TV(A mod pi^h, iid).

    Infinite precision if precision is None.  We use the nonnegative discrepancy
    series sum_k p_q(k)*(1-q^-choose(k,2)*z_k), not 1-minus-truncated-support.
    The omitted tail is at most a_J/a_K^2 * q^-(K+1)^2 /
    (1-q^-(2*K+3)); this follows a_k >= a_infinity >= lower_product.
    """
    K, J = cutoff, product_cutoff
    upper_product = a(q, J)
    lower_product = upper_product * (1-qpower(q,-J)/F(q-1))
    assert lower_product > 0
    z = (lambda k: survival_infinite(q,k)) if precision is None else (
        lambda k: survival(q,k,precision-1))
    series = sum((qpower(q,-k*k)/a(q,k)**2 *
                  (1-qpower(q,-k*(k-1)//2)*z(k)) for k in range(2,K+1)), start=F(0))
    tail = qpower(q,-(K+1)**2)/(lower_product*(1-qpower(q,-(2*K+3))))
    return lower_product*series, upper_product*series+tail


if __name__ == '__main__':
    for q in (2,3,4,5):
        for n in (2,4,8,20):
            print(q, n, float(smith_tv(q,n)),
                  *[float(full_tv(q,n,h)) for h in (1,2,3,None)])
