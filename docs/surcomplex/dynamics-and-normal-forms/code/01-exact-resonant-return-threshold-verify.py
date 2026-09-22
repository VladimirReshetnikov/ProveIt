#!/usr/bin/env python3
"""Exact finite checks for the accompanying research manuscript.

Requires Python 3.10+ and SymPy. This is not an implementation of arbitrary
Hahn fields and is not formal verification of the general theorems.
Run: python verify.py
"""
from __future__ import annotations
import platform
import sympy as sp

x, e, b, t = sp.symbols('x e b t')
checks = 0

def check(name: str, condition: bool) -> None:
    global checks
    if not condition:
        raise AssertionError(name)
    checks += 1
    print(f'PASS {checks:02d}: {name}')

def truncate(p: sp.Expr, order: int) -> sp.Expr:
    return sp.Poly(sp.expand(p), x).as_expr() if sp.degree(p, x) <= order else sp.Add(*[
        sp.expand(p).coeff(x, j) * x**j for j in range(order + 1)])

def compose_truncated(h: sp.Expr, f: sp.Expr, order: int) -> sp.Expr:
    power = sp.Integer(1)
    ans = sp.Integer(0)
    for j in range(order + 1):
        ans = truncate(ans + sp.expand(h).coeff(x, j) * power, order)
        power = truncate(power * f, order)
    return sp.expand(ans)

def valuation_t(p: sp.Expr) -> int:
    """t-valuation of a nonzero rational function with rational coefficients."""
    num, den = sp.fraction(sp.cancel(p))
    if num == 0:
        raise ValueError('valuation_t expects a nonzero input')
    def low(q: sp.Expr) -> int:
        return min(mon[0] for mon, coefficient in sp.Poly(q, t).terms()
                   if coefficient != 0)
    return low(num) - low(den)

def residue_t(p: sp.Expr) -> sp.Expr:
    return sp.simplify(sp.limit(sp.cancel(p), t, 0))

print('Finite symbolic verification')
print(f'Python {platform.python_version()}; SymPy {sp.__version__}')
print('All calculations below use exact symbolic or rational arithmetic.\n')

f = (-1 + e) * x + x**2 + b*x**3
g = sp.Poly(sp.expand(f.subs(x, f)), x)
expected = {
    1: (e-1)**2,
    2: e*(e-1),
    3: (e-1)*(b*e**2-2*b*e+2*b+2),
    4: 3*b*e**2-4*b*e+b+1,
    5: b*(3*b*e**2-6*b*e+3*b+3*e-1),
    6: b*(6*b*e-5*b+1),
    7: 3*b**2*(b*e-b+1),
    8: 3*b**3,
    9: b**4,
}
for j, value in expected.items():
    check(f'general cubic return coefficient b_{j}',
          sp.expand(g.nth(j)-value) == 0)

parabolic = sp.expand(g.as_expr().subs({e: 0, b: -1})-x)
check('tuned return factorization',
      sp.expand(parabolic-x**5*(x**2-2*x+2)*(x**2-x+2)) == 0)
check('tuned degree-3 and degree-4 return cancellation',
      g.nth(3).subs(b, -1).subs(e, 0) == 0 and
      g.nth(4).subs(b, -1).subs(e, 0) == 0)

# Integral exponent representatives of the three valuation regimes.
# delta=8; sigma=2,4,6. The exact radii are 3,2,2.
for sigma, expected_r, expected_p in [
    (2, 3, 1+x**2),
    (4, 2, 1+x**2-2*x**4),
    (6, 2, 1-2*x**4),
]:
    vals = {j: sp.expand(value.subs({e: t**8, b: -1+t**sigma}))
            for j, value in expected.items()}
    c = t**8*(t**8-2)
    r = max(sp.Rational(valuation_t(c)-valuation_t(vals[j]), j-1)
            for j in range(2, 10) if vals[j] != 0)
    check(f'phase sigma={sigma}: exact threshold', r == expected_r)
    P = 1 + sum(residue_t(vals[j] * t**((j-1)*r) / c)*x**(j-1)
                for j in range(2, 10))
    check(f'phase sigma={sigma}: shell polynomial',
          sp.expand(P-expected_p) == 0)
    check(f'phase sigma={sigma}: squarefree shell',
          sp.degree(sp.gcd(P, sp.diff(P, x)), x) == 0)

for P, minimal, ratio in [
    (1+x**2, 1+x**2, -2),
    (1-2*x**4, 1-2*x**4, -4),
    (1+x**2-2*x**4, x**2-1, -6),
    (1+x**2-2*x**4, 2*x**2+1, -3),
]:
    check(f'multiplier ratio {ratio} modulo {minimal}',
          sp.rem(x*sp.diff(P, x)-ratio, minimal, x) == 0)

# Analytic leading coefficient is characterized without choosing fractional
# power branches numerically: check its logarithmic derivative.
for P, logderivative in [
    (1+x**2, 1/x-x/(1+x**2)),
    (1-2*x**4, 1/x+2*x**3/(1-2*x**4)),
    (1+x**2-2*x**4,
     1/x + x/(3*(1-x**2)) - 4*x/(3*(1+2*x**2))),
]:
    check(f'coherent leading coefficient for P={P}',
          sp.cancel(x*P*logderivative-1) == 0)

# Schröder recurrence for finite rational examples, including a nonreal
# multiplier. These are algebraic identity tests, not convergence tests.
for lam, coeffs in [
    (sp.Rational(3, 2), [1, -1]),
    (sp.Rational(-4, 3), [2, 1]),
    (sp.Rational(5, 4), [0, 0, 2]),
    (1+sp.I, [1, -1]),
]:
    N = 9
    F = lam*x + sum(a*x**(j+2) for j, a in enumerate(coeffs))
    powers = {j: compose_truncated(x**j, F, N) for j in range(1, N+1)}
    hs = {1: sp.Integer(1)}
    for n in range(2, N+1):
        rhs = sum(hs[j]*powers[j].coeff(x, n) for j in range(1, n))
        hs[n] = sp.cancel(rhs/(lam-lam**n))
    H = sum(hs[j]*x**j for j in range(1, N+1))
    residual = sp.expand(compose_truncated(H, F, N)-lam*H)
    check(f'Schroeder recurrence through degree {N}, lambda={lam}',
          all(sp.simplify(residual.coeff(x, j)) == 0
              for j in range(N+1)))

# Tangent binomial fixed-point multiplier identity, for several degrees.
for m in range(2, 8):
    c, a = sp.symbols('c a', nonzero=True)
    F = (1+c)*x+a*x**m
    remainder = sp.rem(sp.diff(F, x)-(1-(m-1)*c), x**(m-1)+c/a, x)
    check(f'binomial exact multiplier, degree {m}', sp.simplify(remainder) == 0)

kappa, y = sp.symbols('kappa y')
check('critical-shell discriminant',
      sp.discriminant(1+kappa*y-2*y**2, y) == kappa**2+8)

# A valuation-sensitive check: normalized tuned cubic, e=t^4 and r=1.
# The residue linearizer should be x*(1-2*x^4)^(-1/4).
N = 9
lam = -1+t**4
F = lam*x+t*x**2-t**2*x**3
powers = {j: sp.Poly(sp.expand(F**j), x) for j in range(1, N+1)}
hs = {1: sp.Integer(1)}
for n in range(2, N+1):
    rhs = sum(hs[j]*powers[j].nth(n) for j in range(1, n))
    hs[n] = sp.cancel(rhs/(lam-lam**n))
    expected_residue = {5: sp.Rational(1, 2), 9: sp.Rational(5, 8)}.get(n, 0)
    check(f'tuned normalized coefficient h_{n} is integral',
          hs[n] == 0 or valuation_t(hs[n]) >= 0)
    check(f'tuned residue coefficient h_{n}',
          residue_t(hs[n]) == expected_residue)

print(f'\n{checks}/{checks} finite checks passed.')
print('Not checked by this script: arbitrary Hahn summability, algebraic closure,')
print('maximality for all polynomials, transfinite coherent lifting, or novelty.')
