#!/usr/bin/env python3
"""Checks for the all-multiplicity two-cluster Gamma-face identity.

The exact check compares the proposed polylogarithm formula after a Mobius
substitution with the predecessor's independently derived monomial-face
formula.  Numerical checks compare a one-dimensional beta-kernel integral
with the ordinary spectral polylogarithm series, evaluated by its defining
strict sums and a Hurwitz-zeta tail.  Neither check replaces the proof.
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


@lru_cache(None)
def compositions(n: int, d: int):
    if d == 1:
        return ((n,),) if n >= 1 else ()
    if n < d:
        return ()
    return tuple((a,) + rest for a in range(1, n - d + 2)
                 for rest in compositions(n - a, d - 1))


@lru_cache(None)
def strict_harmonic(n: int, index: tuple[int, ...]) -> F:
    if not index:
        return F(1)
    if n <= 0:
        return F(0)
    return (strict_harmonic(n - 1, index)
            + strict_harmonic(n - 1, index[1:]) / n**index[0])


@lru_cache(None)
def p_coefficient(m: int, r: int, s: int) -> F:
    """Coefficient of z^m in the finite MPL combination P_{r,s}(z)."""
    k = r + s
    return sum((F(math.comb(k - d - 1, r - 1), m)
                * sum((strict_harmonic(m - 1, p)
                       for p in compositions(k - 1, d)), F(0))
                for d in range(1, s + 1)), F(0))


def complete_harmonic(m: int, degree: int) -> F:
    hs = [F(1)] + [F(0)] * degree
    for j in range(1, m):
        for q in range(1, degree + 1):
            hs[q] += hs[q - 1] / j
    return hs[degree]


def predecessor_monomial(m: int, r: int, s: int) -> F:
    """I_{r+s}(B^m; 0 repeated r times, 1 repeated s times)."""
    k = r + s
    return m * sum((math.comb(s, d) * (-1)**(k - d)
                    * math.factorial(k - d) * complete_harmonic(m, k - d)
                    * sum((F(1, math.prod(h)) for h in compositions(m, d)), F(0))
                    for d in range(1, min(s, m) + 1)), F(0))


def exact_checks():
    checks = 0
    for r, s in product(range(1, 5), repeat=2):
        k = r + s
        for m in range(2, 16):
            # q=u/(1+u): compare with the known monomial expansion of
            # I[-log(1+u B)].  These routes have different combinatorics.
            new = ((-1)**(k - 1) * math.factorial(r) * math.factorial(s)
                   * sum((p_coefficient(ell, r, s) * (-1)**(m - ell)
                          * math.comb(m - 1, ell - 1)
                          for ell in range(2, m + 1)), F(0)))
            old = F((-1)**m, m) * predecessor_monomial(m, r, s)
            assert new == old, (r, s, m, new, old)
            checks += 1
            # Classical Landen transformation, in the special combination.
            landed = sum((p_coefficient(ell, s, r) * (-1)**ell
                          * math.comb(m - 1, ell - 1)
                          for ell in range(2, m + 1)), F(0))
            assert landed == p_coefficient(m, r, s), (r, s, m)
            checks += 1
    return checks


def polynomial_mul(a, b, r, s):
    out = {}
    for (i, j), x in a.items():
        for (p, q), y in b.items():
            if i + p <= r and j + q <= s:
                key = i + p, j + q
                out[key] = out.get(key, 0) + x*y
    return out


def beta_kernel(r: int, s: int):
    """Polynomial [X^(r-1)Y^(s-1)] Q(X,Y) exp(X L+Y M)."""
    rr, ss = r - 1, s - 1
    logq = {}
    for i in range(1, rr + 1):
        for j in range(1, ss + 1):
            n = i + j
            logq[i, j] = (sp.Rational((-1)**n * math.comb(n, i), n)
                          * sp.zeta(n))
    q = {(0, 0): sp.Integer(1)}
    term = {(0, 0): sp.Integer(1)}
    for n in range(1, rr + ss + 1):
        term = polynomial_mul(term, logq, rr, ss)
        if not term:
            break
        for key, value in term.items():
            q[key] = q.get(key, 0) + value / sp.factorial(n)
    L, M = sp.symbols('L M')
    expr = sp.expand(sum(v * L**(rr-i) * M**(ss-j)
                         / (sp.factorial(rr-i)*sp.factorial(ss-j))
                         for (i, j), v in q.items()))
    return expr, sp.lambdify((L, M), expr, 'mpmath')


def gamma_g(a, B):
    return 2*mp.re(mp.loggamma(a + 1j*mp.sqrt(B))) - mp.log(2*mp.pi)


def beta_integral(a, B, C, r, s):
    expression, kernel = beta_kernel(r, s)
    fB, fC = gamma_g(a, B), gamma_g(a, C)
    delta = C-B
    def integrand(t):
        if t == 0 or t == 1:
            return mp.mpf(0)
        chord = (gamma_g(a, B+delta*t) - fB) - t*(fC-fB)
        return chord/(t*(1-t))*kernel(mp.log1p(-t), mp.log(t))
    ans = math.factorial(r)*math.factorial(s)*mp.quad(
        integrand, [0, mp.mpf('0.25'), mp.mpf('0.5'), mp.mpf('0.75'), 1])
    return ans, str(expression)


def resolvent(a, C, m):
    """Ordinary sum of ((n+a)^2+C)^(-m), using a short exact Hurwitz tail."""
    n0 = 12
    ans = mp.fsum(((n+a)**2+C)**(-m) for n in range(n0))
    at = a+n0
    coefficient = mp.mpf(1)
    for j in range(180):
        term = coefficient * mp.zeta(2*m+2*j, at)
        ans += term
        if j > 6 and abs(term) < mp.mpf('1e-85'):
            break
        coefficient *= -C*(m+j)/(j+1)
    else:
        raise RuntimeError('Hurwitz tail failed to converge')
    return ans


def spectral_sum(a, B, C, r, s):
    delta = C-B
    # By Tonelli for delta>0, this is exactly the sum over n of the
    # defining strict MPL series.  The finite harmonic coefficients are
    # generated independently of the beta-kernel polynomial.
    ans = mp.mpf(0)
    for m in range(2, 500):
        rat = p_coefficient(m, r, s)
        coefficient = mp.mpf(rat.numerator)/rat.denominator
        term = coefficient*delta**m*resolvent(a, C, m)
        ans += term
        if m > 10 and abs(term) < mp.mpf('1e-75'):
            break
    else:
        raise RuntimeError('Polylogarithm sum failed to converge')
    ans *= (-1)**(r+s-1)*math.factorial(r)*math.factorial(s)
    return ans, m


def numerical_checks():
    mp.mp.dps = 90
    cases = [
        ('two equal displaced masses', '2.3', '0.2', '0.9', 2, 2),
        ('unbounded multiplicity example', '2.3', '0.2', '0.9', 4, 2),
        ('two clusters of size three', '2.3', '0.2', '0.9', 3, 3),
        ('beyond collision Taylor disk', '1.2', '0.2', '2.2', 2, 2),
    ]
    results = []
    for title, aa, bb, cc, r, s in cases:
        a, B, C = map(mp.mpf, (aa, bb, cc))
        left, kernel = beta_integral(a, B, C, r, s)
        right, terms = spectral_sum(a, B, C, r, s)
        error = abs(left-right)
        assert error < mp.mpf('1e-65'), (title, error)
        results.append(dict(case=title, a=aa, B=bb, C=cc, r=r, s=s,
                            beta_kernel=kernel, terms=terms,
                            integral=mp.nstr(left, 70),
                            spectral_sum=mp.nstr(right, 70),
                            absolute_error=mp.nstr(error, 8)))
    return results


if __name__ == '__main__':
    result = dict(exact_assertions=exact_checks(),
                  numerical_precision=90,
                  numerical=numerical_checks(),
                  status='All checks passed; numerical checks are diagnostics, not certificates.')
    target = (Path(__file__).resolve().parent.parent / 'evidence' / 'two_cluster_validation.json')
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
