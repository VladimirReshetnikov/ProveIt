#!/usr/bin/env python3
"""Exact regression checks for Two Derivations Remove the Borel Conjugacy Obstruction.

This is a collection of finite symbolic tests, NOT a proof-assistant verification
of the theorems about infinite supports or Borel classification. No floating-point
approximations or external services are used. Tested with Python 3.13.5 / SymPy 1.14.0.

Run: python verify.py [--output-dir DIRECTORY]
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Run: python -m pip install -r requirements.txt") from exc


t = sp.Symbol("t")
CHECKS: list[dict[str, str]] = []


def check(condition: bool, category: str, name: str) -> None:
    """Record an assertion explicitly, even when Python is run with -O."""
    if not condition:
        raise AssertionError(f"{category}: {name}")
    CHECKS.append({"category": category, "name": name})


def equal(lhs: sp.Expr, rhs: sp.Expr, category: str, name: str) -> None:
    check(sp.cancel(lhs - rhs) == 0, category, name)


def E(f: sp.Expr) -> sp.Expr:
    return t * sp.diff(f, t)


def bracket(a: sp.Expr, b: sp.Expr) -> sp.Expr:
    """Coefficient of [a E, b E]."""
    return sp.cancel(a * E(b) - b * E(a))


def pullback(f: sp.Expr, y: sp.Expr) -> sp.Expr:
    """Theta_y(f); only rational functions are passed to this helper."""
    return sp.cancel(f.subs(t, y))


def scalar_and_pair_checks() -> None:
    category = "scalar and pair normalization"
    # Start with a canonical pair and transport it by several exact coordinates.
    # In K_Q, these positive integer leading exponents all lie in U_Gamma.
    coordinates = [
        t / (1 - t),
        2 * t * (1 + t),
        t**2 * (1 + t),
        3 * t**3 / (1 + t),
    ]
    canonical_scalars = [t, -t, 3 + t, 2 - t, 1 / t, -1 / t]
    normal_coefficients = [1 + t, (1 - 2 * t) / (1 + t)]
    for iy, y in enumerate(coordinates):
        L_y = sp.cancel(E(y) / y)
        for ih, H in enumerate(canonical_scalars):
            A = normal_coefficients[(iy + ih) % len(normal_coefficients)]
            a = sp.cancel(pullback(A, y) / L_y)
            b = sp.cancel(pullback(H * A, y) / L_y)
            h = sp.cancel(b / a)
            tag = f"coordinate {iy + 1}, scalar {ih + 1}"
            equal(h, pullback(H, y), category, f"ratio: {tag}")
            equal(a * E(h), pullback(A * E(H), y), category,
                  f"equivariant j: {tag}")
            equal(bracket(a, b), pullback(bracket(A, H * A), y) / L_y,
                  category, f"bracket covariance: {tag}")
            equal(bracket(a, b), a**2 * E(h), category,
                  f"noncommutator identity: {tag}")

    # Article's explicit inverse-coordinate example.
    y, z = t / (1 - t), t / (1 + t)
    equal(pullback(y, z), t, category, "rational inverse, first direction")
    equal(pullback(z, y), t, category, "rational inverse, second direction")
    equal(pullback(E(y), z), t * (1 + t), category, "normal j in worked example")
    equal(pullback(E(y) / y, z), 1 + t, category,
          "normal A in worked example")

    # A translated finite scalar, in K_Z and K_Q respectively.
    h = 3 - t**2 * (1 + t)**2
    equal(pullback(3 - t**2, t * (1 + t)), h, category, "integer-group scalar")
    equal(pullback(3 - t, t**2 * (1 + t)**2), h, category, "rational-group scalar")
    h = t**-2 + 7 + t
    equal(pullback(1 / t, 1 / h), h, category, "infinite scalar absorbs constant")
    # Verify the squared root equation, not an ambiguous complex square-root rule.
    z_squared = t**2 / (1 + 7 * t**2 + t**3)
    equal(1 / z_squared, h, category, "integer-group root equation")


def lie_checks() -> None:
    category = "Lie identities"
    for p in [sp.Integer(1), sp.Integer(2), sp.Integer(3), sp.Integer(-1),
              sp.Integer(-2)]:
        X, Y = sp.Integer(1) / p, t**p / p
        equal(bracket(X, Y), Y, category, f"affine relation p={p}")
        e, f, H = t**p / p, -t**(-p) / p, sp.Integer(2) / p
        equal(bracket(H, e), 2 * e, category, f"sl2 H,e p={p}")
        equal(bracket(H, f), -2 * f, category, f"sl2 H,f p={p}")
        equal(bracket(e, f), H, category, f"sl2 e,f p={p}")
    samples = [t**-2 + 1, (1 + t) / (1 - t), 2 + t**3]
    a, b, c = samples
    equal(bracket(a, bracket(b, c)) + bracket(b, bracket(c, a))
          + bracket(c, bracket(a, b)), 0, category, "rational Jacobi identity")

    for p, q in [(1, 3), (2, 3), (-1, -3), (-2, -3)]:
        current = t**q
        A, B = sp.Rational(2), sp.Rational(3)
        current *= B
        for n in range(1, 5):
            current = bracket(A * t**p, current)
            expected = B * A**n * sp.prod(q + (j - 1) * p for j in range(n))
            equal(current, expected * t**(q + n * p), category,
                  f"iterated leading coefficient p={p},q={q},n={n}")


def affine_and_bch_checks() -> None:
    category = "affine action and BCH"
    u = sp.Symbol("u")
    a, c = sp.symbols("a c", positive=True)
    b, d = sp.symbols("b d", real=True)
    # Substitution composition applies the left factor to the coefficients
    # and variable in the right factor. This catches the order convention.
    composed = ((u - b) / a - d) / c
    equal(composed, (u - b - a * d) / (a * c), category, "affine group law on u")
    inverse_a, inverse_b = 1 / a, -b / a
    equal(a * inverse_a, 1, category, "affine inverse, dilation")
    equal(b + a * inverse_b, 0, category, "affine inverse, translation")

    # Direct substitution on t when p=1; general p follows via u=t^(-p).
    y_ab, y_cd = a * t / (1 - b * t), c * t / (1 - d * t)
    equal(pullback(y_cd, y_ab), a * c * t / (1 - (b + a * d) * t),
          category, "affine group law on t, p=1")
    for p in [sp.Integer(1), sp.Integer(2), sp.Rational(1, 2), sp.Rational(3, 2)]:
        s, z = sp.symbols("s z")
        # Differentiate the actual scalar formula; evaluate at the identity
        # before simplifying, avoiding unjustified fractional-power rewrites.
        phi_scaling = sp.exp(s / p) * t
        phi_translation = t * (1 - z * t**p)**(-1 / p)
        equal(sp.diff(phi_scaling, s).subs(s, 0), t / p, category,
              f"scaling generator p={p}")
        equal(sp.diff(phi_translation, z).subs(z, 0), t**(p + 1) / p,
              category, f"translation generator p={p}")

    s = sp.Symbol("s")
    F = s / (1 - sp.exp(-s))
    expected = (1 + s / 2 + s**2 / 12 - s**4 / 720 + s**6 / 30240
                - s**8 / 1209600 + s**10 / 47900160)
    computed = sp.series(F, s, 0, 12).removeO()
    equal(computed, expected, category, "BCH coefficients through degree 11")
    v = s * u / (1 - sp.exp(-s))
    check(sp.simplify(v * (sp.exp(s) - 1) / s - sp.exp(s) * u) == 0,
          category, "BCH affine matrix exponential identity")
    check(sp.limit(F, s, 0) == 1, category, "BCH removable value at zero")


def spectrum_checks() -> None:
    category = "finite valuation spectra"
    domain = tuple(range(-4, 5))
    accepted: list[list[int]] = []
    for bits in itertools.product([False, True], repeat=len(domain)):
        S = {v for v, chosen in zip(domain, bits) if chosen}
        closed = all(p + q in S for p in S for q in S if p != q)
        if closed:
            accepted.append(sorted(S))
        # The finite combinatorial theorem has an exact equivalence here.
        allowed = (len(S) <= 1
                   or (len(S) == 2 and 0 in S)
                   or (len(S) == 3 and 0 in S and min(S) == -max(S)))
        check(closed == allowed, category, f"spectrum {sorted(S)}")
    check(len(accepted) == 22, category, "number of admitted spectra in [-4,4]")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    scalar_and_pair_checks()
    lie_checks()
    affine_and_bch_checks()
    spectrum_checks()
    counts: dict[str, int] = {}
    for entry in CHECKS:
        counts[entry["category"]] = counts.get(entry["category"], 0) + 1
    report: dict[str, Any] = {
        "title": "Two Derivations: exact finite regression checks",
        "status": "PASS",
        "assertions_passed": len(CHECKS),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "arithmetic": "Exact rational/symbolic; no numerical tolerances",
        "scope": "Finite regression tests, not a proof-assistant verification",
        "categories": counts,
        "checks": CHECKS,
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "verification_report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    text = (f"{report['title']}\n{'=' * 56}\n"
            f"Status: PASS\nAssertions passed: {len(CHECKS)}\n"
            f"Python: {platform.python_version()}\nSymPy: {sp.__version__}\n\n"
            + "\n".join(f"{name}: {count}" for name, count in counts.items())
            + "\n\nAll arithmetic was exact. These are finite regression tests.\n"
              "They do not verify the Borel, infinite-support, or novelty claims.\n")
    (args.output_dir / "verification_report.txt").write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
