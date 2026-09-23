#!/usr/bin/env python3
"""Exact finite checks for Curve Rigidity over the Omnific Integers.

These checks do NOT verify the arbitrary-support or scheme-theoretic theorems.
They check polynomial certificates and finite-support models of the algebraic
identities used in the written proofs. No floating-point arithmetic is used.

Requires Python >= 3.10 and SymPy. Run: python3 verify.py
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time
from typing import Iterable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install requirements.txt before running.") from exc

Exponent = tuple[Fraction, ...]


class CheckFailure(RuntimeError):
    """An exact certificate or finite algebraic check failed."""


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def require(self, group: str, condition: bool, detail: str) -> None:
        if not condition:
            raise CheckFailure(f"{group}: {detail}")
        self.counts[group] += 1

    def zero(self, group: str, expression: sp.Expr, detail: str) -> None:
        self.require(group, sp.expand(expression) == 0, detail)


@dataclass
class Series:
    """A finite rational-coefficient Hahn series in a lexicographic group."""
    rank: int
    coefficients: dict[Exponent, Fraction]

    def __post_init__(self) -> None:
        if self.rank < 1:
            raise ValueError("Rank must be positive.")
        clean: dict[Exponent, Fraction] = {}
        for exponent, coefficient in self.coefficients.items():
            if len(exponent) != self.rank:
                raise ValueError("Exponent rank mismatch.")
            exponent = tuple(Fraction(t) for t in exponent)
            coefficient = Fraction(coefficient)
            if coefficient:
                clean[exponent] = clean.get(exponent, Fraction(0)) + coefficient
        self.coefficients = {e: c for e, c in clean.items() if c}

    @property
    def zero_exponent(self) -> Exponent:
        return (Fraction(0),) * self.rank

    @property
    def degree(self) -> Exponent | None:
        return max(self.coefficients) if self.coefficients else None

    @property
    def constant(self) -> Fraction:
        return self.coefficients.get(self.zero_exponent, Fraction(0))

    def _compatible(self, other: Series) -> None:
        if self.rank != other.rank:
            raise ValueError("Cannot combine different ranks.")

    def __add__(self, other: Series) -> Series:
        self._compatible(other)
        result = dict(self.coefficients)
        for e, c in other.coefficients.items():
            result[e] = result.get(e, Fraction(0)) + c
        return Series(self.rank, result)

    def __mul__(self, other: Series) -> Series:
        self._compatible(other)
        result: dict[Exponent, Fraction] = {}
        for e, c in self.coefficients.items():
            for f, d in other.coefficients.items():
                exponent = tuple(a + b for a, b in zip(e, f))
                result[exponent] = result.get(exponent, Fraction(0)) + c * d
        return Series(self.rank, result)

    def derivative(self, weights: Exponent) -> Series:
        if len(weights) != self.rank:
            raise ValueError("Functional rank mismatch.")
        return Series(self.rank, {
            e: c * sum((a * b for a, b in zip(e, weights)), Fraction(0))
            for e, c in self.coefficients.items()
        })


def random_series(rng: random.Random, rank: int, region: str) -> Series:
    result: dict[Exponent, Fraction] = {}
    zero = (Fraction(0),) * rank
    for _ in range(rng.randint(3, 9)):
        e = tuple(Fraction(rng.randint(-5, 5), rng.randint(1, 4))
                  for _ in range(rank))
        if (region == "B" and e < zero) or (region == "O" and e > zero):
            e = tuple(-t for t in e)
        c = Fraction(rng.randint(-7, 7), rng.randint(1, 5))
        result[e] = result.get(e, Fraction(0)) + c
    return Series(rank, result)


def check_symbolic(checks: Checks) -> dict[str, object]:
    x, y, a, b, dx, dy, u, r, n, t = sp.symbols("x y a b dx dy u r n t")
    f = x**3 + a*x + b
    delta = 4*a**3 + 27*b**2
    U = 27*b - 18*a*x
    V = 4*a**2 + 6*a*x**2 - 9*b*x
    checks.zero("cubic", U*f + V*sp.diff(f, x) - delta,
                "generic cubic Bezout identity")
    lhs = delta*dx - y*(U*y*dx + 2*V*dy)
    rhs = U*(f-y**2)*dx + V*(sp.diff(f, x)*dx - 2*y*dy)
    checks.zero("cubic", lhs-rhs, "off-equation differential certificate")
    checks.zero("cubic", sp.discriminant(f, x) + delta,
                "cubic discriminant sign")

    polynomials = [sp.prod(x-j for j in range(d)) for d in range(2, 9)]
    polynomials += [x**3+x+1, x**4+x+1, x**5-x+1, x**7+3*x+2]
    certificate_count = 0
    for f in polynomials:
        fp = sp.diff(f, x)
        checks.require("superelliptic", sp.gcd(f, fp) == 1,
                       f"squarefreeness: {f}")
        U, V, gcd = sp.gcdex(f, fp, x)
        checks.require("superelliptic", gcd == 1, "normalized gcd")
        checks.zero("superelliptic", U*f+V*fp-1, "Bezout polynomial")
        for m in range(2, 9):
            lhs = dx-y**(m-1)*(U*y*dx+m*V*dy)
            rhs = U*(f-y**m)*dx+V*(fp*dx-m*y**(m-1)*dy)
            checks.zero("superelliptic", lhs-rhs, f"certificate m={m}, f={f}")
            certificate_count += 1

    for d in range(2, 31):
        for m in range(2, 31):
            obstruction = d*(m-1)-m
            checks.require("degree_obstruction",
                           (obstruction == 0 if (d, m) == (2, 2)
                            else obstruction > 0), f"d={d}, m={m}")

    X, Y = u**2-2*r, u**3-3*r*u
    checks.zero("parametrizations", Y**2-(X**3-3*r*r*X+2*r**3),
                "generic singular cubic parametrization")
    checks.zero("parametrizations", (u**3)**2-(u**2)**3, "cusp")
    checks.zero("parametrizations", n**2+2*n*t+t**2-(n+t)**2,
                "entire parabola constant-term fiber")
    checks.zero("parametrizations", (n+t)-n-t, "parabola inverse parameter")

    z = sp.symbols("z")
    q = sum(sp.binomial(sp.Rational(1, 2), j)*(a*z**2+b*z**3)**j
            for j in range(5))
    residual = sp.Poly(sp.expand(q*q-(1+a*z**2+b*z**3)), z)
    for j in range(10):
        checks.zero("binomial", residual.nth(j), f"square-root residual z^{j}")
    qpoly = sp.Poly(sp.expand(q), z)
    checks.zero("binomial", qpoly.nth(2)-a/2, "first elliptic correction")
    checks.zero("binomial", qpoly.nth(3)-b/2, "second elliptic correction")
    q0 = sum(sp.binomial(sp.Rational(1, 2), j)*z**(2*j) for j in range(11))
    residual0 = sp.Poly(sp.expand(q0*q0-(1+z*z)), z)
    for j in range(22):
        checks.zero("binomial", residual0.nth(j), f"normality example z^{j}")
    for j in range(1, 41):
        checks.require("lexicographic_clearing", (Fraction(1), Fraction(1-2*j)) > (0, 0),
                       f"positive shifted exponent j={j}")
        checks.require("lexicographic_clearing", 1-2*j < 0,
                       f"unshifted negative exponent j={j}")
        checks.require("lexicographic_clearing", sp.binomial(sp.Rational(1, 2), j) != 0,
                       f"nonzero binomial coefficient j={j}")
    return {"superelliptic_polynomials": len(polynomials),
            "superelliptic_differential_certificates": certificate_count,
            "degree_grid": {"d": [2, 30], "m": [2, 30]}}


def check_finite_hahn(checks: Checks) -> dict[str, object]:
    seed = 20260923
    rng = random.Random(seed)
    trials_per_rank = 80
    for rank in (1, 2, 3):
        zero = (Fraction(0),) * rank
        for trial in range(trials_per_rank):
            f = random_series(rng, rank, "all")
            g = random_series(rng, rank, "all")
            weights = tuple(Fraction(rng.randint(-5, 5), rng.randint(1, 4))
                            for _ in range(rank))
            df, dg = f.derivative(weights), g.derivative(weights)
            checks.require("finite_hahn", (f*g).derivative(weights) == df*g+f*dg,
                           f"Leibniz rank={rank}, trial={trial}")
            checks.require("finite_hahn", (f+g).derivative(weights) == df+dg,
                           "linearity")
            checks.require("finite_hahn", set(df.coefficients) <= set(f.coefficients),
                           "support preservation")
            if df.degree is not None:
                checks.require("finite_hahn", f.degree is not None and df.degree <= f.degree,
                               "nonincreasing derivative degree")
            if f.degree is not None and g.degree is not None:
                expected = tuple(a+b for a, b in zip(f.degree, g.degree))
                checks.require("finite_hahn", (f*g).degree == expected, "degree additivity")

            fb, gb = random_series(rng, rank, "B"), random_series(rng, rank, "B")
            fo = random_series(rng, rank, "O")
            db, do = fb.derivative(weights), fo.derivative(weights)
            checks.require("finite_hahn", all(e >= zero for e in (fb*gb).coefficients),
                           "B is multiplicatively closed")
            checks.require("finite_hahn", (fb*gb).constant == fb.constant*gb.constant,
                           "constant-term retraction on B")
            checks.require("finite_hahn", all(e >= zero for e in db.coefficients),
                           "D(B) contained in B")
            checks.require("finite_hahn", all(e < zero for e in do.coefficients),
                           "D(O) contained in maximal ideal")
            checks.require("finite_hahn", not (set(fb.coefficients) & set(do.coefficients)),
                           "opposite support intersection")
            if fb.degree is not None and fb.degree > zero:
                j = next(j for j, component in enumerate(fb.degree) if component != 0)
                w = [Fraction(0)]*rank
                w[j] = 1/fb.degree[j]
                detected = fb.derivative(tuple(w))
                checks.require("finite_hahn", detected.degree == fb.degree,
                               "functional normalized on the leading exponent")
                checks.require("finite_hahn",
                               detected.coefficients[fb.degree] == fb.coefficients[fb.degree],
                               "leading coefficient retained by normalized functional")

        e = (Fraction(1),) + (Fraction(0),)*(rank-1)
        monomial = Series(rank, {e: Fraction(1)})
        inverse = Series(rank, {tuple(-t for t in e): Fraction(1)})
        checks.require("constant_term_boundary", (monomial*inverse).constant == 1,
                       "constant coefficient of inverse monomial product")
        checks.require("constant_term_boundary", monomial.constant*inverse.constant == 0,
                       "constant extraction is not a field homomorphism")
    return {"ranks": [1, 2, 3], "trials_per_rank": trials_per_rank, "seed": seed,
            "coefficients": "fractions.Fraction", "order": "lexicographic"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    started = time.perf_counter()
    checks = Checks()
    report: dict[str, object] = {
        "title": "Finite exact verification for Curve Rigidity over the Omnific Integers",
        "run_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "proof_boundary": (
            "Checks only finite symbolic identities and finite-support rational Hahn models. "
            "Not a verification of arbitrary Hahn support, properness, Riemann-Roch, "
            "global generation, class-size arguments, or the scheme-valued rigidity theorems."
        ),
    }
    try:
        report["symbolic_cases"] = check_symbolic(checks)
        report["finite_hahn_cases"] = check_finite_hahn(checks)
        report["status"] = "passed"
        exit_code = 0
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
        exit_code = 1
    report["assertions_by_group"] = dict(sorted(checks.counts.items()))
    report["total_assertions"] = sum(checks.counts.values())
    report["elapsed_seconds"] = round(time.perf_counter()-started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
