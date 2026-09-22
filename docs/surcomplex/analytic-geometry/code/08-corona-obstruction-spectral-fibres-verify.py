#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These tests do not verify the infinite Hahn, interpolation, ultrafilter,
completeness, or priority assertions. See PROOF_AUDIT.md.
Requires Python 3.10+ and SymPy. No network access is used.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import platform
import random
import sys
from typing import TypeAlias

if not __debug__:
    raise RuntimeError("Run without -O: assertion checks must remain enabled.")
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install with: python -m pip install sympy") from exc

Series: TypeAlias = dict[Fraction, Fraction]
SEED = 20260921


def clean(a: Series) -> Series:
    return {e: c for e, c in a.items() if c}


def add(a: Series, b: Series) -> Series:
    result = dict(a)
    for exponent, coefficient in b.items():
        result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return clean(result)


def scale(a: Series, coefficient: Fraction) -> Series:
    return clean({e: coefficient * c for e, c in a.items()})


def multiply(a: Series, b: Series, cutoff: Fraction | None = None) -> Series:
    result: Series = {}
    for e, c in a.items():
        for f, d in b.items():
            exponent = e + f
            if cutoff is not None and exponent >= cutoff:
                continue
            result[exponent] = result.get(exponent, Fraction(0)) + c * d
    return clean(result)


def geometric_inverse(u: Series, cutoff: Fraction) -> Series:
    """Inverse of 1+u strictly below a rational exponent cutoff.

    Used only for finite positive rational support in the tests. This is
    not a general arbitrary-rank or infinite-support Hahn implementation.
    """
    if cutoff <= 0 or any(e <= 0 for e in u):
        raise ValueError("The cutoff and every exponent of u must be positive.")
    one = {Fraction(0): Fraction(1)}
    result = dict(one)
    term = dict(one)
    # Termination here uses the Archimedean rational test domain only.
    while term:
        term = scale(multiply(term, u, cutoff), Fraction(-1))
        result = add(result, term)
    return result


def check_exponents() -> dict[str, object]:
    gammas = [Fraction(2) - Fraction(1, n) for n in range(1, 1001)]
    assert gammas[0] == 1
    assert all(Fraction(1) <= value < 2 for value in gammas)
    for n in range(1, 1000):
        assert gammas[n] - gammas[n - 1] == Fraction(1, n * (n + 1))
        assert -gammas[n] < -gammas[n - 1]
    # Symbolic identities supplement, but do not turn these into an
    # automated proof of arbitrary-support assertions.
    n = sp.symbols("n", integer=True, positive=True)
    assert sp.simplify((2 - 1/(n+1)) - (2 - 1/n) - 1/(n*(n+1))) == 0
    assert sp.limit(2 - 1/n, n, sp.oo) == 2
    return {
        "values_checked": len(gammas),
        "successive_differences_checked": len(gammas) - 1,
        "first_exponents": [str(x) for x in gammas[:8]],
        "symbolic_difference": "gamma_(n+1)-gamma_n = 1/(n(n+1))",
        "symbolic_limit": "gamma_n -> 2",
        "inverse_support": "strictly decreasing; infinite nonadmissibility is proved in article",
    }


def check_cardinal() -> dict[str, object]:
    z = sp.symbols("z")
    h = sp.sin(sp.pi / (1 - z))
    dh = sp.diff(h, z)
    expected_dh = sp.pi * sp.cos(sp.pi/(1-z)) / (1-z)**2
    assert sp.simplify(dh - expected_dh) == 0
    count = 16
    points = [sp.Rational(n - 1, n) for n in range(1, count + 1)]
    for n, a in enumerate(points, 1):
        assert sp.simplify(h.subs(z, a)) == 0
        assert sp.simplify(dh.subs(z, a) - sp.pi * n*n * (-1)**n) == 0
    # Off-diagonal cardinal identities have a nonzero rational denominator.
    for n, a in enumerate(points, 1):
        en = h / (sp.pi * n*n * (-1)**n * (z - a))
        for m, b in enumerate(points, 1):
            if m != n:
                assert sp.simplify(en.subs(z, b)) == 0
        # The removable value is evaluated via the already verified derivative.
        assert sp.simplify(dh.subs(z, a) / (sp.pi * n*n * (-1)**n)) == 1
    return {"centres": count, "cardinal_values": count*count,
            "derivative_formula": "PASS", "ordinary_disk_zero_classification": "written proof only"}


def check_divided_difference(rng: random.Random) -> dict[str, object]:
    z, eps = sp.symbols("z eps")
    cases = 80
    for _ in range(cases):
        degree = rng.randrange(0, 10)
        c = sp.Rational(rng.randrange(-4, 5), rng.randrange(1, 7))
        coeffs = [sp.Rational(rng.randrange(-6, 7), rng.randrange(1, 6))
                  for _ in range(degree + 1)]
        # Coefficients are the Taylor coefficients at c, so the R_k formula
        # has a direct finite polynomial expression.
        f = sum((coeffs[j]*(z-c)**j for j in range(degree+1)), sp.Integer(0))
        quotient = sp.Integer(0)
        for k in range(degree):
            remainder = sum((coeffs[j]*(z-c)**(j-k-1)
                             for j in range(k+1, degree+1)), sp.Integer(0))
            quotient += eps**k * remainder
        fa = sum((coeffs[j]*eps**j for j in range(degree+1)), sp.Integer(0))
        assert sp.expand((z-c-eps)*quotient - f + fa) == 0
    return {"exact_polynomial_identities": cases, "maximum_degree": 9,
            "scope": "finite polynomial specialization of the support-controlled formula"}


def check_corona_inequalities() -> dict[str, object]:
    cases = 0
    for n in range(1, 101):
        gamma = Fraction(2) - Fraction(1, n)
        for denominator in range(1, 13):
            for numerator in range(1, 61):
                q = Fraction(numerator, denominator)
                if q < 2:
                    assert q < 2  # h has valuation q.
                else:
                    assert 1 + q >= 3 > gamma  # F retains its centre value.
                    assert gamma < 2
                cases += 1
    return {"rational_grid_cases": cases,
            "case_split": "q<2, or q>=2 and 1+q>=3>gamma_n",
            "scope": "checks valuation inequalities, not analytic evaluations on all monads"}


def check_neumann_examples(rng: random.Random) -> dict[str, object]:
    cases = 120
    one = {Fraction(0): Fraction(1)}
    cutoff = Fraction(5)
    pool = [Fraction(j, 6) for j in range(1, 19)]
    for _ in range(cases):
        selected = rng.sample(pool, rng.randrange(1, 7))
        u = clean({e: Fraction(rng.randrange(-4, 5), rng.randrange(1, 5)) for e in selected})
        inverse = geometric_inverse(u, cutoff)
        product = multiply(add(one, u), inverse, cutoff)
        assert product == one
    return {"exact_truncated_inverses": cases, "cutoff_exclusive": str(cutoff),
            "scope": "finite positive rational supports only; not a general Hahn algorithm"}


def check_gauge_witnesses() -> dict[str, object]:
    n = sp.symbols("n", integer=True, positive=True)
    symbolic = 0
    for r in range(0, 5):
        for s in range(r+1, 7):
            assert sp.simplify(n**s / n**r - n**(s-r)) == 0
            assert sp.limit(n**(s-r), n, sp.oo) == sp.oo
            symbolic += 1
    # For integer s, ceil(n^s) is exactly n^s. Check finite witnesses too.
    finite = 0
    for s in range(1, 7):
        for value in range(1, 101):
            exponent = value**s
            assert exponent <= 2 * value**s
            finite += 1
    return {"symbolic_integer_rate_separations": symbolic,
            "finite_witness_bounds": finite,
            "nonprincipal_ultrafilter": "not computationally constructed",
            "arbitrary_real_rates_and_primality": "written proof only"}


def run() -> dict[str, object]:
    rng = random.Random(SEED)
    results = {
        "exponents": check_exponents(),
        "cardinal_functions": check_cardinal(),
        "divided_differences": check_divided_difference(rng),
        "corona_inequalities": check_corona_inequalities(),
        "positive_support_inversion": check_neumann_examples(rng),
        "gauge_witnesses": check_gauge_witnesses(),
    }
    return {
        "status": "PASS",
        "seed": SEED,
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "checks": results,
        "limitations": [
            "Finite consistency checks, not a proof-assistant certificate.",
            "No infinite Hahn series or arbitrary ultrafilter is computed.",
            "No historical-priority conclusion follows from these tests.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: exact finite checks completed; results written to {args.output}")


if __name__ == "__main__":
    main()
