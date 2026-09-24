#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

This is NOT an implementation of all surreal numbers or of the full
Berarducci--Mantova derivation. The finite Hahn core uses Q(i) coefficients,
Q exponents, t = omega**(-1), and D(t**q) = -q*t**(q+1).
Classification decisions use the theorems proved in the article; example
tests do not constitute proofs of nonexistence for arbitrary Hahn series.

Run: python verify_examples.py
Dependency: SymPy (tested version is printed on execution).
No network, file writes, external evaluators, or floating-point computations.
"""
from __future__ import annotations

from collections import Counter
from typing import Mapping
import platform

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

Polynomial = dict[s.Rational, s.Expr]
R = s.Rational
I = s.I
COUNTS: Counter[str] = Counter()


def canonical(terms: Mapping[object, object]) -> Polynomial:
    """Validate and normalize an already constructed exact finite input.

    Strings and floats are deliberately rejected; this is not an expression
    parser. Both real and imaginary coefficient components must be rational.
    """
    out: Polynomial = {}
    for exponent, coefficient in terms.items():
        if not isinstance(exponent, (int, s.Integer, s.Rational)):
            raise TypeError("Exponents must be exact rational numbers")
        if not isinstance(coefficient, (int, s.Expr)):
            raise TypeError("Coefficients must be exact Gaussian-rational expressions")
        q = R(exponent)
        c = s.expand(coefficient)
        real, imag = c.as_real_imag()
        if real.is_Rational is not True or imag.is_Rational is not True:
            raise TypeError("Coefficient is not in Q(i)")
        if c != 0:
            out[q] = c
    return dict(sorted(out.items()))


def add(a: Polynomial, b: Polynomial) -> Polynomial:
    out = dict(a)
    for q, c in b.items():
        out[q] = out.get(q, s.S.Zero) + c
    return canonical(out)


def multiply(a: Polynomial, b: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for q, c in a.items():
        for r, d in b.items():
            out[q + r] = out.get(q + r, s.S.Zero) + c * d
    return canonical(out)


def derivative(a: Polynomial) -> Polynomial:
    return canonical({q + 1: -q * c for q, c in a.items()})


def primitive(a: Polynomial) -> Polynomial:
    """Return the normalized primitive inside C((t^Q)), or reject resonance."""
    if a.get(R(1), 0) != 0:
        raise ValueError("[t^1] input is nonzero: no primitive in C((t^Q))")
    return canonical({q - 1: -c / (q - 1) for q, c in a.items() if q != 1})


def ambient_primitive_pair(a: Polynomial) -> tuple[Polynomial, s.Expr]:
    """Return (p, c) denoting the exact ambient primitive p + c*log(omega)."""
    c = a.get(R(1), s.S.Zero)
    return primitive({q: value for q, value in a.items() if q != 1}), c


def classify(a: Polynomial) -> str:
    """Classify nonzero solutions of D(y)=a*y for a finite exact coefficient."""
    imaginary_support = [q for q, c in a.items() if s.im(c) != 0]
    ambient = not imaginary_support or min(imaginary_support) > 1
    workspace = all(q >= 1 for q in a) and s.im(a.get(R(1), 0)) == 0
    if workspace:
        return "workspace"
    return "ambient-only" if ambient else "phase-obstructed"


def workspace_certificate(a: Polynomial) -> tuple[s.Rational, Polynomial]:
    """Return (r, k) certifying y=t^r E(k); requires positive support of k."""
    if classify(a) != "workspace":
        raise ValueError("No nonzero solution in the declared Hahn workspace")
    r = R(-a.get(R(1), 0))
    k = primitive({q: c for q, c in a.items() if q > 1})
    if any(q <= 0 for q in k):
        raise AssertionError("Internal error: exponential argument is not infinitesimal")
    return r, k


def check(group: str, condition: object, description: str) -> None:
    if not bool(condition):
        raise AssertionError(f"{group}: {description}")
    COUNTS[group] += 1


def equal(group: str, lhs: s.Expr, rhs: s.Expr, description: str) -> None:
    check(group, s.simplify(s.expand(lhs - rhs)) == 0, description)


def run() -> None:
    t, x, z = s.symbols("t x z", positive=True)
    dt = lambda f: -t**2 * s.diff(f, t)

    # Monomial primitives, including negative and fractional support shifts.
    exponents = sorted({R(n, d) for d in (1, 2, 3, 5) for n in range(-6, 9)})
    for q in exponents:
        monomial = canonical({q: 2 + 3*I})
        expected = canonical({q + 1: -q * (2 + 3*I)})
        check("rational monomials", derivative(monomial) == expected, f"D at {q}")
        if q != 1:
            check("rational monomials", derivative(primitive(monomial)) == monomial,
                  f"primitive at {q}")

    # Deterministic mixed polynomials, exact sparse product rule.
    samples = [canonical({R(-j, 2): 1 + j*I, R(j + 1, 3): j - I,
                          R(j + 3): 2}) for j in range(7)]
    samples += [{}, canonical({0: 1})]
    for j, a in enumerate(samples):
        for k, b in enumerate(samples):
            check("finite product rule", derivative(multiply(a, b)) ==
                  add(multiply(derivative(a), b), multiply(a, derivative(b))),
                  f"pair {j}, {k}")

    # The t resonance is separated explicitly; an ambient primitive is a pair.
    for value in (1, 2 + I, -3*I):
        a = canonical({R(-2): 3, R(1): value, R(5, 2): 1 - I})
        p, c = ambient_primitive_pair(a)
        check("additive resonance", add(derivative(p), canonical({1: c})) == a,
              "ambient primitive pair")
        try:
            primitive(a)
        except ValueError:
            check("additive resonance", True, "resonance rejected")
        else:
            raise AssertionError("resonance was not rejected")

    cases = [
        ({}, "workspace"),
        ({0: 1}, "ambient-only"),
        ({1: 2}, "workspace"),
        ({1: I}, "phase-obstructed"),
        ({2: I}, "workspace"),
        ({R(3, 2): I}, "workspace"),
        ({R(1, 2): I}, "phase-obstructed"),
        ({-2: 1, 2: I}, "ambient-only"),
        ({1: R(-3, 2), 2: 1 + 2*I}, "workspace"),
        ({0: I}, "phase-obstructed"),
        ({R(-1, 3): 2, R(4, 3): 7*I}, "ambient-only"),
    ]
    for terms, expected in cases:
        a = canonical(terms)
        check("solution classification", classify(a) == expected, repr(terms))
        if expected == "workspace":
            r, k = workspace_certificate(a)
            check("solution certificates", add(canonical({1: -r}), derivative(k)) == a,
                  repr(terms))
            check("solution certificates", all(q > 0 for q in k), "positive support")

    # Validation rejects non-exact or unsupported data instead of guessing.
    for bad in ({0.5: 1}, {0: 0.1}, {0: s.sqrt(2)}, {"1/2": 1}):
        try:
            canonical(bad)
        except TypeError:
            check("input validation", True, repr(bad))
        else:
            raise AssertionError(f"Unsupported input accepted: {bad}")

    # Quotient identities in the t model.
    rational_examples = [1+t, 1+t+t**2, t**-2 + 3*t, t**3-I*t, 2-I*t**2]
    for a in rational_examples:
        for b in rational_examples:
            equal("quotient rule", dt(a/b), (b*dt(a)-a*dt(b))/b**2, "quotient")

    # Phase primitives: these are exact symbolic derivative identities only.
    for B, b in [(-1/x, x**-2), (-2/s.sqrt(x), x**R(-3, 2)),
                 (s.log(x), 1/x), (s.log(s.log(x)), 1/(x*s.log(x))),
                 (-1/s.log(x), 1/(x*s.log(x)**2))]:
        equal("phase primitive identities", s.diff(B, x), b, str(B))

    # The two derivative terms are verified separately and together.
    for P, h in [(x*z + x**-1*z**2, x**2),
                 ((x**2+1)*z**3 + (1+I)/x, x**-1),
                 (x**3*z + I*x*z**2, x+1)]:
        lhs = s.diff(P.subs(z, h), x)
        rhs = s.diff(P, x).subs(z, h) + s.diff(P, z).subs(z, h)*s.diff(h, x)
        equal("two-derivative chain rule", lhs, rhs, str(P))

    # Corrected integration identity and its nonzero constant correction.
    f, g = canonical({0: 1}), canonical({2: 1})
    jf, jg = primitive(f), primitive(g)
    product = multiply(jf, jg)
    inner = add(multiply(f, jg), multiply(jf, g))
    normalized = primitive(inner)
    correction = canonical({0: product.get(R(0), 0)})
    check("normalized integration", product == add(normalized, correction), "corrected identity")
    check("normalized integration", product != normalized, "uncorrected identity fails")
    check("normalized integration", correction == canonical({0: -1}), "constant equals -1")

    # Exact finite inverse of D-i on polynomials in omega.
    for degree in range(13):
        P = sum((j+1+I*(degree-j))*x**j for j in range(degree+1))
        y = I*sum((-I)**j * s.diff(P, x, j) for j in range(degree+1))
        equal("finite inhomogeneous inverse", s.diff(y, x)-I*y, P, f"degree {degree}")

    # Real characteristic-root kernels: finite symbolic checks of displayed modes.
    for lam in (-2, 0, 3):
        for degree in range(5):
            residual = s.exp(lam*x)*x**degree
            for _ in range(degree+1):
                residual = s.diff(residual, x) - lam*residual
            equal("real characteristic modes", residual, s.S.Zero, f"{lam}, {degree}")

    # Finite formal Taylor checks. They do not establish infinite summability.
    order = 12
    e = sum((-I*t)**n/s.factorial(n) for n in range(order+1))
    residual = s.Poly(s.expand(dt(e)-I*t**2*e), t)
    for n in range(order+2):
        equal("formal Taylor coefficients", residual.nth(n), s.S.Zero, f"local exp coefficient {n}")
    l = sum((-1)**(n+1)*t**n/R(n) for n in range(1, order+1))
    log_residual = s.series(dt(l) + t**2/(1+t), t, 0, order+2).removeO()
    equal("formal Taylor coefficients", log_residual, s.S.Zero, "local log derivative through order 13")
    e1 = sum(t**n/s.factorial(n) for n in range(order+1))
    e2 = sum((2*I*t)**n/s.factorial(n) for n in range(order+1))
    e12 = sum(((1+2*I)*t)**n/s.factorial(n) for n in range(order+1))
    discrepancy = s.Poly(s.expand(e1*e2-e12), t)
    for n in range(order+1):
        equal("formal Taylor coefficients", discrepancy.nth(n), s.S.Zero, f"group law coefficient {n}")

    print("Surreal differential algebra: exact finite verification")
    print(f"Python {platform.python_version()}; SymPy {s.__version__}")
    for group, count in COUNTS.items():
        print(f"PASS {count:4d}  {group}")
    print(f"TOTAL: {sum(COUNTS.values())} checks passed; 0 failures")
    print("Scope: finite Q(i)-coefficient Q-exponent algebra and symbolic/formal examples only.")
    print("Not checked: full BM construction, arbitrary Hahn summability, or general theorems.")


if __name__ == "__main__":
    run()
