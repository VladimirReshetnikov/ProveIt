#!/usr/bin/env python3
"""Exact cutoff-contact replay and independent numerical diagnostics.

Run: python verification/verify_cutoff_jets.py [output.json]
Dependencies: sympy, mpmath. Numerical checks are not interval proofs.
The contact identities are checked by Euler-polynomial arithmetic, independently
of evaluating any divergent infinite series.
"""
from functools import lru_cache
import json
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp

s, x, shift = sp.symbols("s x shift")
exact = []
numeric = []


@lru_cache(None)
def a(j):
    return sp.expand((-1)**j * sp.euler(j, 0) * sp.rf(s, j)
                     / (2 * sp.factorial(j)))


@lru_cache(None)
def c(k):
    if k == 0:
        return sp.Rational(1, 4)
    return sp.expand(-sum(a(j) * a(k-j) for j in range(1, k)))


def assert_zero(name, expression):
    assert sp.expand(expression) == 0, (name, expression)
    exact.append(name)


contact_table = []
for m in range(13):
    # Direct Euler specialization of the endpoint, not its quadratic shortcut.
    numerator = sp.Poly(sp.euler(m, x) * sp.euler(m, x+1) / 4, x)
    direct_contact = numerator.nth(m)
    assert_zero(f"Euler endpoint contact m={m}", c(m).subs(s, -m)-direct_contact)

    translated = sp.expand(sum(c(k) * sp.prod(-s-k-j for j in range(m-k))
                                * shift**(m-k) / sp.factorial(m-k)
                                for k in range(m+1)))
    quotient = sp.div(numerator.as_expr(), x**m, x)[0]
    assert_zero(f"translated zeroth contact m={m}",
                translated.subs(s, -m)-quotient.subs(x, shift))

    order_two_euler = sum(sp.binomial(m, j)*sp.euler(j, shift+1)
                          * sp.euler(m-j, 0) for j in range(m+1))
    assert_zero(f"translated top jet m={m}",
                sp.diff(translated, s, m)-(-1)**m*order_two_euler/4)
    assert_zero(f"all higher jets vanish m={m}", sp.diff(translated, s, m+1))
    if m % 2:
        assert_zero(f"natural odd contacts vanish m={m}", c(m))
    else:
        assert_zero(f"sharp even top jet m={m}",
                    sp.diff(c(m), s, m)+sp.euler(m+1, 0)/2)
    contact_table.append({"m":m, "c_m":str(sp.factor(c(m))),
                          "zeroth_contact":str(direct_contact),
                          "top_derivative":str(sp.diff(c(m), s, m))})

# Independent product/shift expansion, without the recurrence shortcut.
for k in range(9):
    coeff = 0
    for j in range(k+1):
        for ell in range(k-j+1):
            power = k-j-ell
            binomial = sp.prod(-s-ell-v for v in range(power))/sp.factorial(power)
            coeff += a(j)*a(ell)*binomial
    assert_zero(f"direct shifted product coefficient k={k}", coeff-c(k))

mp.mp.dps = 55


def B(order, z):
    if order == 1:
        return (mp.digamma((z+1)/2)-mp.digamma(z/2))/2
    return mp.power(2, -order)*(mp.zeta(order, z/2)-mp.zeta(order, (z+1)/2))


def F(order, z):
    return mp.power(z, order)*B(order, z)*B(order, z+1)


def finite(order, z, N):
    return mp.fsum((mp.power(n+z+1, order)-mp.power(n+z, order))
                   * B(order, n+z+1)**2 for n in range(N+1))


def record(name, lhs, rhs, tolerance="1e-43"):
    residual = abs(lhs-rhs)
    assert residual < mp.mpf(tolerance)*max(1, abs(lhs), abs(rhs)), (name, residual)
    numeric.append({"name":name, "absolute_residual":mp.nstr(residual, 12),
                    "lhs":mp.nstr(lhs, 35), "rhs":mp.nstr(rhs, 35)})


for order,z in [(mp.mpc("0.7","0.3"),mp.mpc("0.8","0.2")),
                (mp.mpf("-2.4"),mp.mpf("0.7")),
                (mp.mpc("-0.3","0.2"),mp.mpf("1.3"))]:
    N = 7
    record(f"finite identity s={order},a={z}", finite(order,z,N),F(order,z)-F(order,N+z+1))

for order,jet in [(0,1),(0,2),(-2,1),(-2,2),(-1,3)]:
    z,N=mp.mpf("0.8"),4
    record(f"finite differentiated identity s={order},r={jet}",
           mp.diff(lambda u:finite(u,z,N),order,jet),
           mp.diff(lambda u:F(u,z)-F(u,N+z+1),order,jet))


def logrho(z):
    return mp.log(z/2)/2+mp.loggamma(z/2)-mp.loggamma((z+1)/2)


for z in [mp.mpf("0.7"),mp.mpc("1.2","0.3")]:
    record(f"second spectral derivative Gamma endpoint a={z}",
           mp.diff(lambda u:F(u,z),0,2),mp.log(z)**2/4-2*logrho(z)**2)

aa,bb,N=mp.mpf("0.8"),mp.mpf("1.4"),30
def log_summand(n):
    da,db=mp.log((n+aa+1)/(n+aa)),mp.log((n+bb+1)/(n+bb))
    return da*logrho(n+bb)+db*logrho(n+aa)-da*db/2
record("polarized logarithmic Gamma finite certificate",
       mp.fsum(log_summand(n) for n in range(N+1)),
       2*(logrho(aa)*logrho(bb)-logrho(N+aa+1)*logrho(N+bb+1)))

# Independent quadrature for the inherited cyclotomic coefficient.
integral=mp.quad(lambda t:mp.log(t)*mp.log1p(-t)/(1+t*t),[0,mp.mpf(".5"),1])
closed=mp.im(mp.polylog(3,(1+1j)/2))-mp.pi*mp.log(2)**2/32-mp.pi**3/128
record("cyclotomic coefficient: quadrature versus trilogarithm",integral,closed)

result={"status":"passed", "exact_check_count":len(exact),
        "numerical_check_count":len(numeric), "decimal_precision":mp.mp.dps,
        "numerical_scope":"diagnostic residuals, not certified interval bounds",
        "exact_checks":exact, "contacts":contact_table,"numerical_checks":numeric}
output=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/"results"/"cutoff_jets_checks.json"
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"status":"passed","exact_checks":len(exact),
                  "numerical_checks":len(numeric),"output":str(output)}))
