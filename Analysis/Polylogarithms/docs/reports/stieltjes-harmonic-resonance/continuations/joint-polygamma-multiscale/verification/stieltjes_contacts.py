"""Exact finite contact compiler for the article's monomial collision theorem.

The returned expression is the change from the specified coincident finite
part F[m,n,r,t].  Exponents are exact positive rationals.  No numerical
limit, quadrature, or conjectural integer-relation search is used.

Examples:
    collision_correction(0, 0, 1, 0, 2, 1) + zeta(2)
        == -1 - zeta(3)
    collision_correction(1, 0, 0, 0, 3, 2)
        == zeta(2) - Rational(5, 4)
"""
from __future__ import annotations

import sympy as sp

u, v, s = sp.symbols("u v s")


def _trunc(expr, max_u, max_v):
    p = sp.Poly(sp.expand(expr), u, v)
    return sp.Add(*(c * u**a * v**b for (a, b), c in p.terms()
                    if a <= max_u and b <= max_v))


def _exp_jet(logarithm, max_u, max_v):
    """Exponential of a zero-constant polynomial, in a finite quotient ring."""
    ans = term = sp.Integer(1)
    for k in range(1, max_u + max_v + 1):
        term = _trunc(term * logarithm / k, max_u, max_v)
        ans += term
    return _trunc(ans, max_u, max_v)


def gamma_derivative_at_one(index, order):
    """gamma_index^(order)(1), using zeta order derivatives if order > 0."""
    if order == 0:
        return sp.stieltjes(index)
    p = sp.Poly(sp.rf(1 + v, order), v)
    answer = 0
    for k in range(index + 1):
        d = index - k
        pc = p.nth(d) * sp.factorial(d)
        zk = (sp.zeta(order + 1) if k == 0 else
              sp.Subs(sp.diff(sp.zeta(s), s, k), s, order + 1))
        answer += sp.binomial(index, k) * pc * zk
    return (-1)**(index + order) * answer


def singular_contact(m, n, r, t, j, lam=1, mu=1):
    """(-1)^(m+n) d_u^m d_v^n H_j(0,0), evaluated by finite jets.

    The Gamma reflection quotient is replaced by its ordinary-zeta
    expansion, so the removable pole is never numerically divided by zero.
    """
    lam, mu = sp.sympify(lam), sp.sympify(mu)
    R, N, degree = r + t + 1, r + t + 1 + j, m + n + 1
    left = -sp.log(lam) * u - sp.log(mu) * v
    right = -sp.log(mu) * (u + v)
    for h in range(1, degree + 1):
        left += sp.harmonic(j, h) * u**h / h
        left += (-1)**(h + 1) * sp.harmonic(N - 1, h) * v**h / h
        right += (-1)**(h + 1) * sp.harmonic(N - 1, h) * (u + v)**h / h
        if h >= 2:
            right += sp.zeta(h) * (u**h + (-1)**h *
                                  ((u + v)**h - v**h)) / h
    numerator = (_exp_jet(left, m + 1, n) -
                 _exp_jet(right, m + 1, n))
    # Division by u after cancellation is coefficient extraction at m+1.
    coeff = sp.Poly(numerator, u, v).coeff_monomial(u**(m + 1) * v**n)
    scale = ((-1)**(m + n + t) * sp.factorial(m) * sp.factorial(n) *
             sp.factorial(N - 1) / sp.factorial(j) * lam**j / mu**(R + j))
    return sp.simplify(scale * coeff)


def _mixed_contact(m, n, r, t, alpha, beta, lam, mu):
    A = sp.Poly(sp.rf(1 + u, r) / sp.factorial(r), u)
    critical = ((-sp.log(lam))**(m + 1) / sp.factorial(m + 1)
                - A.nth(m + 1))
    answer = ((-1)**(m + r) * sp.factorial(m) * critical *
              gamma_derivative_at_one(n, r + t))
    for k in range(r):
        ell = alpha * (r - k) / beta
        if ell.q != 1:
            continue
        ell = int(ell)
        p = sp.Poly(sp.rf(1 + u, r - k - 1), u)
        coeff = sum(p.nth(h) * (-sp.log(lam))**(m - h) /
                    sp.factorial(m - h) for h in range(m + 1))
        answer += ((-1)**(m + r) * sp.factorial(m) *
                   mu**ell * lam**(k - r) / sp.factorial(ell) * coeff *
                   gamma_derivative_at_one(n, t + k + ell))
    return sp.simplify(answer)


def collision_correction(m, n, r, t, alpha, beta, lam=1, mu=1):
    """Exact correction to F[m,n,r,t] for positive rational exponents.

    For equal exponents, the formula reduces to the previous fixed-rate
    contact law; no singular--singular constant then occurs.
    """
    indices = (m, n, r, t)
    if any(not isinstance(k, int) or k < 0 for k in indices):
        raise ValueError("indices must be nonnegative Python integers")
    alpha, beta = sp.Rational(alpha), sp.Rational(beta)
    lam, mu = sp.sympify(lam), sp.sympify(mu)
    if alpha <= 0 or beta <= 0:
        raise ValueError("exponents must be positive")
    if lam.is_positive is not True or mu.is_positive is not True:
        raise ValueError("rates must be explicitly positive")
    if alpha < beta:
        return collision_correction(n, m, t, r, beta, alpha, mu, lam)
    answer = _mixed_contact(m, n, r, t, alpha, beta, lam, mu)
    answer += _mixed_contact(n, m, t, r, beta, alpha, mu, lam)
    if alpha != beta:
        j = beta * (r + t + 1) / (alpha - beta)
        if j.q == 1:
            answer += singular_contact(m, n, r, t, int(j), lam, mu)
    return sp.simplify(answer)


if __name__ == "__main__":
    for alpha, beta in [(2, 1), (3, 1), (4, 1), (5, 1), (3, 2), (5, 3)]:
        value = collision_correction(0, 0, 1, 0, alpha, beta) + sp.zeta(2)
        print(f"ordered constant, exponents ({alpha},{beta}): {sp.simplify(value)}")
    for j in range(1, 5):
        print(f"first Stieltjes contact, j={j}: "
              f"{collision_correction(1, 0, 0, 0, j + 1, j)}")
