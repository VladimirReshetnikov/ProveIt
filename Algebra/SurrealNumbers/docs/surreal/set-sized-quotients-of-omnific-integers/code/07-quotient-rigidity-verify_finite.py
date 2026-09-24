#!/usr/bin/env python3
"""Finite algebra checks accompanying the omnific quotient manuscript.

This does NOT implement surreal numbers or check any class-sized argument.
It verifies finite identities underlying the support and CRT proofs.
Requires Python >= 3.10 and SymPy. No floating-point arithmetic is used.
"""
from __future__ import annotations

import argparse
import json
import platform
from fractions import Fraction
from pathlib import Path
from typing import TypeAlias

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install it with 'python -m pip install sympy'.") from exc

Exponent: TypeAlias = tuple[int, int, int]
Laurent: TypeAlias = dict[Exponent, Fraction]


def clean(p: Laurent) -> Laurent:
    return {e: c for e, c in p.items() if c != 0}


def multiply(p: Laurent, q: Laurent) -> Laurent:
    result: Laurent = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(e[k] + f[k] for k in range(3))
            result[g] = result.get(g, Fraction(0)) + c * d
    return clean(result)


def run_checks() -> dict:
    checks: list[str] = []

    def check(name: str, condition: bool) -> None:
        if not bool(condition):
            raise AssertionError(f"FAILED: {name}")
        checks.append(name)

    # Lexicographic exponents encode a >> delta > eta > 0.
    # No choice of small floating-point real numbers substitutes for this order.
    for r, s in [(1, 1), (2, 3), (-2, 5), (7, -3)]:
        r, s = Fraction(r), Fraction(s)
        for n in range(1, 21):
            quotient = {(1, -1 - k, k): (s / r) ** k / r for k in range(n)}
            divisor = {(0, 1, 0): r, (0, 0, 1): -s}
            expected = {(1, 0, 0): Fraction(1), (1, -n, n): -(s / r) ** n}
            tag = f"weighted_difference_r={r}_s={s}_N={n}"
            check(tag, multiply(divisor, quotient) == clean(expected))
            check(tag + "_positive_exponents", all(e > (0, 0, 0) for e in quotient))
            check(tag + "_positive_remainder", (1, -n, n) > (0, 0, 0))

    # Finite truncation of the binomial division expansion, in a Laurent ring.
    t = sp.Symbol("t")
    for n in range(1, 11):
        remainder = sum((j + 1) ** 2 * t**j for j in range(n))
        for count in (1, 2, 3, 5, 8):
            quotient = sum((-1)**k * remainder * t**(-(k + 1)*n)
                           for k in range(count))
            expected = remainder * (1 - (-1)**count * t**(-count*n))
            residual = sp.expand((1 + t**n) * quotient - expected)
            check(f"binomial_finite_remainder_n={n}_N={count}", residual == 0)
            centers = [Fraction(j, n) - k - 1
                       for k in range(count) for j in range(n)]
            check(f"binomial_distinct_blocks_n={n}_N={count}",
                  len(set(centers)) == n * count)

    # Exact first idempotents in Q(sqrt(2))[y] / (y^4 + 1).
    y = sp.Symbol("y")
    sqrt2 = sp.sqrt(2)
    modulus = y**4 + 1

    def reduced(expression):
        return sp.Poly(sp.rem(sp.expand(expression), modulus, y,
                              extension=sqrt2), y, extension=sqrt2).as_expr()

    u = y**2
    zeta = (1 + u) / sqrt2
    zeta_inverse = (1 - u) / sqrt2
    plus = (1 + y*zeta_inverse)/2
    minus = (1 - y*zeta_inverse)/2
    for name, expression in [
        ("imaginary_unit", u**2 + 1),
        ("zeta_square", zeta**2 - u),
        ("zeta_inverse", zeta*zeta_inverse - 1),
        ("plus_idempotent", plus**2 - plus),
        ("minus_idempotent", minus**2 - minus),
        ("orthogonality", plus*minus),
        ("partition_of_one", plus + minus - 1),
    ]:
        check(name, reduced(expression) == 0)
    for name, expression in [("plus", plus), ("minus", minus)]:
        check(name + "_nonzero", reduced(expression) != 0)
        check(name + "_not_one", reduced(expression - 1) != 0)

    # Coordinate descriptions of the CRT idempotents and refinement maps.
    # These arrays are certificates for finite product algebra, not a proof
    # that it injects into the ambient omnific quotient.
    for level in range(7):
        m = 2**level
        basis = [tuple(int(j == k) for j in range(m)) for k in range(m)]
        check(f"CRT_level={level}_partition", all(sum(e[j] for e in basis) == 1
                                                 for j in range(m)))
        for k, e in enumerate(basis):
            check(f"CRT_level={level}_idempotent={k}",
                  tuple(v*v for v in e) == e and any(e))
            lift = tuple(e[j % m] for j in range(2*m))
            refined = tuple(int(j == k) + int(j == k + m) for j in range(2*m))
            check(f"CRT_level={level}_refinement={k}", lift == refined)
        check(f"CRT_level={level}_orthogonality",
              all(not any(e[j]*f[j] for j in range(m))
                  for k, e in enumerate(basis) for ell, f in enumerate(basis) if k < ell))

    # First seven disjoint dyadic valuation classes at a common finite level.
    m = 2**8
    indicators = [tuple(int(z % (2**(j + 1)) == 2**j) for z in range(m))
                  for j in range(7)]
    check("dyadic_disjoint_sequence_nonzero", all(any(f) for f in indicators))
    check("dyadic_disjoint_sequence_orthogonal",
          all(not any(f[z]*g[z] for z in range(m))
              for j, f in enumerate(indicators) for k, g in enumerate(indicators) if j < k))

    return {
        "status": "passed",
        "check_count": len(checks),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "checks": checks,
        "scope": "Exact finite identities only; no arbitrary Hahn series or proper-class proofs.",
        "not_verified": [
            "Conway normal-form theorem and identification of omnific integers",
            "Existence of positive surreal lower bounds for set-sized supports",
            "Proper-class/small-target collision argument",
            "Infinite support admissibility and nonmembership in the localization",
            "Full manuscript, historical novelty, or any Lean proof",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {result['check_count']} exact finite checks. Output: {args.output}")
    print(result["scope"])


if __name__ == "__main__":
    main()
