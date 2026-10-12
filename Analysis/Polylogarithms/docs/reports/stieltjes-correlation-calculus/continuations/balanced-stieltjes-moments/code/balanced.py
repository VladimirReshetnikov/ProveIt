"""Balanced Stieltjes kernels and numerical Mellin diagnostics.

All evaluations use ordinary mpmath arithmetic, not certified intervals.
The Euler--Maclaurin and large-x expansions are truncated; use parameter
variation and the analytic proofs, not residuals alone, to assess an identity.
"""
from __future__ import annotations
from functools import lru_cache
from math import factorial, comb
from typing import Iterable, NamedTuple
import mpmath as mp


@lru_cache(maxsize=None)
def pochhammer_coefficients(n: int, degree: int) -> tuple[int, ...]:
    """Exact integer coefficients of (1+z)_n through the requested degree."""
    if n < 0 or degree < 0:
        raise ValueError("n and degree must be nonnegative")
    c = [1] + [0] * degree
    for k in range(1, n + 1):
        c = [k*c[j] + (c[j-1] if j else 0) for j in range(degree + 1)]
    return tuple(c)


def elementary(m: int) -> list:
    """Coefficients of product_{j=1}^{m-1}(1+z/j)."""
    if m < 1:
        raise ValueError("m must be positive")
    c = [mp.mpf(1)]
    for j in range(1, m):
        c = [(c[k] if k < len(c) else 0) + (c[k-1]/j if k else 0)
             for k in range(len(c)+1)]
    return c


class Kernel:
    """Precomputed EM data; construct after setting mp.mp.dps."""
    def __init__(self, q: int, n: int = 56, r: int = 40):
        if q < 0 or n < 1 or r < 1:
            raise ValueError("Require q >= 0, n >= 1, r >= 1")
        self.q, self.n, self.r = q, n, r
        self.data = []
        for j in range(1, r+1):
            p = pochhammer_coefficients(2*j-1, q)
            weights = tuple(factorial(q)//factorial(q-k)*p[k]
                            for k in range(min(q,2*j-1)+1))
            self.data.append((2*j, mp.bernoulli(2*j)/mp.factorial(2*j), weights))

    def __call__(self, x, a):
        x, a = mp.mpf(x), mp.mpf(a)
        if x <= 0 or a <= 0:
            raise ValueError("This evaluator requires positive real x and a")
        q = self.q
        A = x+a+self.n
        L = -mp.log1p((a+self.n)/x)
        out = mp.fsum((-mp.log1p((a+j)/x))**q/(x+a+j)
                      for j in range(self.n))
        out += L**(q+1)/(q+1) + L**q/(2*A)
        for power, b, weights in self.data:
            poly = mp.fsum(w*L**(q-k) for k,w in enumerate(weights))
            out += b*A**(-power)*poly
        return out


def tail_coefficient(k: int, q: int, a):
    if k <= q:
        return mp.mpf(0)
    return ((-1)**k*mp.bernpoly(k,a)/mp.factorial(k)*factorial(q)
            *pochhammer_coefficients(k-1,q)[q])


def kappa(m: int, q: int):
    if not q >= m >= 1:
        raise ValueError("kappa requires q >= m >= 1")
    return ((-1)**(m+q)*mp.factorial(q)/m
            *mp.fsum((-1)**j*e*mp.zeta(q+1-j)
                     for j,e in enumerate(elementary(m))))


def master_rhs(u, q: int, a):
    """Use away from positive integer u (integer limits have separate formulas)."""
    g = mp.diff(lambda z: mp.gamma(u+z)/mp.gamma(1+z), mp.mpf(0), q)
    return mp.gamma(1-u)*mp.zeta(1-u,a)*g


class Term(NamedTuple):
    coefficient: object
    q: int
    a: object
    log_power: int = 0


def mellin_integral(u, terms: Iterable[Term], *, n=56, r=40, cutoff=64,
                    tail_order=64):
    """Numerical integral of a combined kernel, with an integrated EM tail.

    All terms are combined BEFORE integration. This matters when individual
    shifted terms diverge. A near-zero coefficient may be discarded only in
    an analytically known convergent case; this routine is not a convergence
    oracle. Its purpose is verification of hypotheses already proved.
    """
    terms = [Term(mp.mpf(t.coefficient), t.q, mp.mpf(t.a), t.log_power)
             for t in terms]
    if not terms or any(t.log_power < 0 for t in terms):
        raise ValueError("Provide nonempty terms with nonnegative log powers")
    T = mp.mpf(cutoff)
    if T <= max(t.a for t in terms)+1 or tail_order < max(t.q for t in terms)+2:
        raise ValueError("Increase cutoff or tail_order")
    kernels = {q: Kernel(q,n,r) for q in {t.q for t in terms}}
    def integrand(x):
        L = mp.log(x)
        return x**(u-1)*mp.fsum(t.coefficient*L**t.log_power*kernels[t.q](x,t.a)
                                for t in terms)
    core = (mp.quad(lambda t: 4*t**3*integrand(t**4), [0,1])
            + mp.quad(integrand, [1,5,T]))
    # Combine coefficients, so cancelled powers are never integrated apart.
    tail = mp.mpf(0)
    tolerance = mp.power(10,-mp.mp.dps+8)
    for k in range(1,tail_order+1):
        for ell in {t.log_power for t in terms}:
            ck = mp.fsum(t.coefficient*tail_coefficient(k,t.q,t.a)
                         for t in terms if t.log_power == ell)
            if mp.re(u) >= k:
                if abs(ck) > tolerance:
                    raise ValueError(f"Uncancelled divergent tail: power={k}, log={ell}")
                continue
            moment = T**(u-k)*mp.fsum(comb(ell,j)*mp.log(T)**(ell-j)
                                        *factorial(j)/(k-u)**(j+1)
                                        for j in range(ell+1))
            tail += ck*moment
    return core+tail


def stieltjes_terms(n: int, nodes, coefficients, log_power: int = 0):
    """Invert the balanced binomial transform for a zero-total-mass filter."""
    if abs(mp.fsum(coefficients)) > mp.power(10,-mp.mp.dps+5):
        raise ValueError("The filter must have total mass zero")
    return [Term(c*((-1)**q)*comb(n,q), q, a, log_power+n-q)
            for a,c in zip(nodes,coefficients) for q in range(n+1)]
