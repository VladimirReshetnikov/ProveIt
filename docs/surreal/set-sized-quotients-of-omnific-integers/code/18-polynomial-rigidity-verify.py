#!/usr/bin/env python3
"""Exact, finite regression checks for Polynomial Rigidity of Omnific Integer Lattices.

These are not formal proofs of the surreal statements. H is a formal variable:
Q[H] and Q(i)[H] provide finite-support examples with positive integer exponents.
No implementation of arbitrary surreal arithmetic, order, or support is claimed.
Run with Python 3 and SymPy. The JSON record is written beside this script.
"""
from __future__ import annotations

import json
import platform
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from random import Random

import sympy as sp

X, Y, H = sp.symbols("X Y H")
I = sp.I
rng = Random(20260923)
counts: Counter[str] = Counter()


def check(category: str, condition: bool, description: str) -> None:
    if not bool(condition):
        raise AssertionError(f"{category}: {description}")
    counts[category] += 1


def equal(category: str, left: sp.Expr, right: sp.Expr, description: str) -> None:
    check(category, sp.cancel(sp.expand(left - right)) == 0, description)


def ct(expr: sp.Expr) -> sp.Expr:
    """Constant coefficient for a polynomial in the formal infinite variable H."""
    return sp.expand(expr).coeff(H, 0)


def pure(expr: sp.Expr) -> sp.Expr:
    return sp.expand(expr - ct(expr))


def binom_poly(var: sp.Expr, degree: int) -> sp.Expr:
    return sp.prod(var - j for j in range(degree)) / sp.factorial(degree)


def difference(expr: sp.Expr, var: sp.Symbol, count: int = 1) -> sp.Expr:
    for _ in range(count):
        expr = sp.expand(expr.subs(var, var + 1) - expr)
    return expr


def gaussian_integer(expr: sp.Expr) -> bool:
    re, im = sp.expand_complex(sp.simplify(expr)).as_real_imag()
    return re.is_integer is True and im.is_integer is True


def omnific_polynomial(expr: sp.Expr, gaussian: bool = False) -> bool:
    """Only checks this restricted finite-support model, not arbitrary surreals."""
    try:
        poly = sp.Poly(sp.expand(expr), H, extension=I) if gaussian else sp.Poly(expr, H, domain=sp.QQ)
    except (sp.PolynomialError, sp.polys.polyerrors.CoercionFailed):
        return False
    c = poly.nth(0)
    return gaussian_integer(c) if gaussian else c.is_integer is True


def canonical_candidate(expr: sp.Expr) -> sp.Expr | None:
    poly = sp.Poly(expr, X)
    degree = poly.degree()
    lead = poly.LC()
    if pure(lead) != 0:
        return None
    return sp.cancel(-pure(poly.nth(degree - 1)) / (degree * lead))


# Finite Newton interpolation: deterministic rational-coefficient examples.
for degree in range(8):
    for trial in range(3):
        f = sum(sp.Rational(rng.randint(-9, 9), rng.randint(1, 7)) * X**j
                for j in range(degree + 1))
        reconstruction = sum(difference(f, X, j).subs(X, 0) * binom_poly(X, j)
                             for j in range(degree + 1))
        equal("newton_univariate", f, reconstruction, f"degree bound {degree}, trial {trial}")

for degree in range(6):
    f = sum(sp.Rational(rng.randint(-7, 7), rng.randint(1, 5)) * X**a * Y**b
            for a in range(degree + 1) for b in range(degree + 1 - a))
    reconstruction = sp.S.Zero
    for a in range(degree + 1):
        for b in range(degree + 1 - a):
            delta = difference(difference(f, X, a), Y, b).subs({X: 0, Y: 0})
            reconstruction += delta * binom_poly(X, a) * binom_poly(Y, b)
    equal("newton_multivariate", f, reconstruction, f"total degree bound {degree}")

# Restricted finite-support substitutions in the classified integer-valued ring.
f = H**2 * X**3 + H * X / 7 + binom_poly(X, 3)
for trial in range(40):
    a = sp.Integer(rng.randint(-12, 12)) + sum(
        sp.Rational(rng.randint(-7, 7), rng.randint(1, 9)) * H**j for j in range(1, 4)
    )
    value = sp.expand(f.subs(X, a))
    check("real_finite_support", omnific_polynomial(value), f"trial {trial} lies in Z + H Q[H]")
    equal("constant_term_transfer", ct(value), binom_poly(ct(a), 3), f"trial {trial}")

# Gaussian example works; the real binomial polynomial need not.
gaussian_f = (X**2 - X) / (1 + I)
for a in range(-5, 6):
    for b in range(-5, 6):
        value = sp.simplify(gaussian_f.subs(X, a + I*b))
        check("gaussian_integer_values", gaussian_integer(value), f"node {a}+i*{b}")
for trial in range(20):
    c = rng.randint(-4, 4) + I * rng.randint(-4, 4)
    a = c + (sp.Rational(rng.randint(-4, 4), 3) + I * sp.Rational(rng.randint(-4, 4), 5))*H + H**2/7
    value = sp.expand(gaussian_f.subs(X, a))
    check("gaussian_finite_support", omnific_polynomial(value, gaussian=True), f"trial {trial}")
    equal("gaussian_constant_term", ct(value), gaussian_f.subs(X, c), f"trial {trial}")
equal("gaussian_counterexamples", binom_poly(I, 2), (-1-I)/2, "real binomial value at i")
check("gaussian_counterexamples", not gaussian_integer(binom_poly(I, 2)), "real binomial is not Gaussian integer-valued")

# Recover the unique center from the top two coefficients, then test whole identity.
eta = H + H**2/3
beta = H**3/5
for degree in range(1, 7):
    p = binom_poly(X, degree) + 2*X + 3
    # Degree one has ordinary leading coefficient 3, not 1; no assumption is made.
    f = sp.expand(p.subs(X, X-eta))
    recovered = canonical_candidate(f)
    check("canonical_center", recovered is not None, f"ordinary leading coefficient, degree {degree}")
    equal("canonical_center", recovered, eta, f"recovered center, degree {degree}")
    equal("canonical_center", f.subs(X, X+recovered), p, f"full translated identity, degree {degree}")
    equal("canonical_center", ct(f), p, f"reduction, degree {degree}")
    if degree >= 2:
        two_sided = f + beta
        recovered = canonical_candidate(two_sided)
        equal("translated_targets", recovered, eta, f"input center, degree {degree}")
        equal("translated_targets", pure(two_sided.subs(X, recovered)), beta, f"output center, degree {degree}")
        equal("translated_targets", two_sided.subs(X, X+recovered), p+beta, f"full two-sided identity, degree {degree}")

# Deliberately add a nonconstant infinite obstruction below the top two coefficients.
for degree in range(3, 7):
    p = X**degree + X + 1
    f = sp.expand(p.subs(X, X-eta) + H*(X-eta))
    recovered = canonical_candidate(f)
    equal("failed_center_tests", recovered, eta, f"candidate remains fixed, degree {degree}")
    equal("failed_center_tests", pure(f.subs(X, X+recovered)), H*X, f"remaining nonconstant obstruction, degree {degree}")
    check("failed_center_tests", sp.expand(f.subs(X, X+recovered)-ct(f)) != 0, f"ordinary-output identity rejected, degree {degree}")
for degree in range(1, 7):
    check("infinite_leading_coefficients", canonical_candidate(H*X**degree+X+1) is None,
          f"infinite leading coefficient, degree {degree}")

# Exact composition obstruction, with generic ordinary leading coefficients.
for m in range(2, 6):
    for n in range(2, 6):
        p = 2*X**m + X + 3
        q = 3*X**n + 2*X + 1
        delta = H + H**2/7
        aligned = sp.expand(p.subs(X, q) + beta)
        misaligned = sp.expand(p.subs(X, q+delta) + beta)
        equal("composition_alignment", pure(aligned), beta, f"aligned pair ({m},{n})")
        poly = sp.Poly(misaligned, X)
        equal("composition_obstruction", pure(poly.nth(m*n-1)), 0, f"next-to-leading coefficient ({m},{n})")
        expected = m*2*3**(m-1)*delta
        equal("composition_obstruction", pure(poly.nth((m-1)*n)), expected, f"obstruction coefficient ({m},{n})")
        check("composition_obstruction", expected != 0, f"nonzero obstruction ({m},{n})")

# Sharp examples: exact roots (the proof, not these tests, excludes all other inputs).
for degree in range(2, 9):
    f = sp.prod(X-j*H for j in range(1, degree+1))
    for j in range(1, degree+1):
        equal("sharp_family_roots", f.subs(X, j*H), 0, f"degree {degree}, root {j}H")
equal("sharp_family_roots", (H*X).subs(X, 0), 0, "degree-one replacement")

# Leading-coefficient Lagrange identity with formal, infinitely separated nodes.
for degree in range(1, 5):
    f = sum((H/(j+1)+j+2)*X**j for j in range(degree+1))
    nodes = [j*H+j*j for j in range(degree+1)]
    reconstructed_lead = sum(f.subs(X, node) / sp.prod(node-other for other in nodes if other != node)
                             for node in nodes)
    equal("lagrange_leading_identity", reconstructed_lead, sp.Poly(f, X).LC(), f"degree {degree}")

# Exact forward differences of a nonzero proper rational function.
u = 1/(X+3)
for order in range(8):
    expected = (-1)**order * sp.factorial(order) / sp.prod(X+3+j for j in range(order+1))
    equal("proper_rational_differences", u, expected, f"order {order}")
    u = sp.cancel(u.subs(X, X+1)-u)

# Nilpotent matrices read off every coefficient; matrix counterexamples.
for degree in range(1, 7):
    size = degree+1
    N = sp.zeros(size)
    for j in range(size-1):
        N[j, j+1] = 1
    coeffs = [sp.Rational(j+1, j+2) + H*(j+1) for j in range(degree+1)]
    matrix_value = sp.zeros(size)
    for j, a in enumerate(coeffs):
        matrix_value += a * (N**j)
    for j, a in enumerate(coeffs):
        equal("nilpotent_coefficient_readout", matrix_value[0,j], a, f"degree {degree}, coefficient {j}")
N = sp.Matrix([[0,1],[0,0]])
equal("matrix_counterexamples", ((N*N-N)/2)[0,1], -sp.Rational(1,2), "real scalar-preserver fails on N")
equal("matrix_counterexamples", ((N*N-N)/(1+I))[0,1], -1/(1+I), "Gaussian scalar-preserver fails on N")

# Hasse-Taylor identity modulo epsilon^(s+1), exact in finite polynomial rings.
eps = sp.Symbol("eps")
for degree in range(7):
    f = sum((H+j+1)*X**j/sp.factorial(j+1) for j in range(degree+1))
    for order in range(degree+1):
        hasse = sp.diff(f, X, order) / sp.factorial(order)
        equal("hasse_taylor", sp.expand(f.subs(X,X+eps)).coeff(eps,order), hasse,
              f"degree {degree}, order {order}")

record = {
    "title": "Polynomial Rigidity of Omnific Integer Lattices: exact finite checks",
    "status": "PASS",
    "total_assertions": sum(counts.values()),
    "categories": dict(sorted(counts.items())),
    "random_seed": 20260923,
    "python_version": platform.python_version(),
    "sympy_version": sp.__version__,
    "executed_at_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Exact identities and finite-support Q[H] / Q(i)[H] examples only.",
    "not_verified_by_this_program": [
        "arbitrary surreal normal forms or their order",
        "quantification over the full omnific proper class",
        "general theorem proofs in a proof assistant",
        "historical novelty or literature completeness",
    ],
}
output = Path(__file__).resolve().with_name("verification_results.json")
output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
print(json.dumps(record, indent=2))
