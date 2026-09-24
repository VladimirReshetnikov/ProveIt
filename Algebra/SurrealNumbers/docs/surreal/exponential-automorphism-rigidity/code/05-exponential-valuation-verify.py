#!/usr/bin/env python3
"""Exact checks for Exponential Rigidity from Valuation Data.

Python 3.10+; standard library only. These are finite algebra checks, not
formal verification of surreal-number, valuation, or proper-class theorems.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import platform
import random
import sys
from typing import TypeAlias

Coefficient: TypeAlias = Fraction
Laurent: TypeAlias = dict[int, Coefficient]
Monomial: TypeAlias = tuple[int, int, int, int]
Poly: TypeAlias = dict[Monomial, Coefficient]


def check(condition: bool, message: str) -> None:
    """Checks are kept explicit as well as rejecting optimized Python mode."""
    if not condition:
        raise AssertionError(message)


def laurent_add(a: Laurent, b: Laurent) -> Laurent:
    out = a.copy()
    for n, c in b.items():
        out[n] = out.get(n, Fraction(0)) + c
        if not out[n]:
            del out[n]
    return out


def scale(a: Laurent, scalar: Fraction) -> Laurent:
    return {n: scalar * c for n, c in a.items() if scalar * c}


def laurent_mul(a: Laurent, b: Laurent, cutoff: int | None = None) -> Laurent:
    out: Laurent = {}
    for n, c in a.items():
        for m, d in b.items():
            if cutoff is not None and n + m > cutoff:
                continue
            out[n + m] = out.get(n + m, Fraction(0)) + c * d
    return {n: c for n, c in out.items() if c}


def truncate(a: Laurent, cutoff: int) -> Laurent:
    return {n: c for n, c in a.items() if n <= cutoff and c}


def binomial_integer(n: int, k: int) -> int:
    """Generalized binomial(n,k), including negative integer n."""
    if k < 0:
        return 0
    if n >= 0:
        return comb(n, k) if k <= n else 0
    return (-1) ** k * comb(k - n - 1, k)


def substitute_phi(a: Laurent, cutoff: int) -> Laurent:
    """Compute a(t+t^2) through exponent cutoff for a Laurent polynomial."""
    out: Laurent = {}
    for n, c in a.items():
        for k in range(max(0, cutoff - n + 1)):
            value = c * binomial_integer(n, k)
            if value:
                out[n + k] = out.get(n + k, Fraction(0)) + value
    return {n: c for n, c in out.items() if c}


def derivative(a: Laurent) -> Laurent:
    """D=t^2 d/dt on Laurent polynomials."""
    return {n + 1: n * c for n, c in a.items() if n != 0 and c}


def valuation(a: Laurent) -> int | None:
    """None is +infinity (the valuation of zero)."""
    return min(a) if a else None


def poly_add(a: Poly, b: Poly, multiplier: int = 1) -> Poly:
    out = a.copy()
    for monomial, c in b.items():
        out[monomial] = out.get(monomial, Fraction(0)) + multiplier * c
    return {m: c for m, c in out.items() if c}


def poly_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for m, c in a.items():
        for n, d in b.items():
            power = tuple(m[j] + n[j] for j in range(4))
            out[power] = out.get(power, Fraction(0)) + c * d
    return {m: c for m, c in out.items() if c}


def variable(index: int) -> Poly:
    power = [0, 0, 0, 0]
    power[index] = 1
    return {tuple(power): Fraction(1)}


def verify_universal_identities() -> int:
    a, b, A, B = [variable(j) for j in range(4)]
    # (AB-ab)-A(B-b)-b(A-a) = 0, in Q[a,b,A,B].
    displacement = poly_add(poly_mul(A, B), poly_mul(a, b), -1)
    residual = poly_add(displacement, poly_mul(A, poly_add(B, b, -1)), -1)
    residual = poly_add(residual, poly_mul(b, poly_add(A, a, -1)), -1)
    check(not residual, "Universal displacement identity failed")

    # Variables a,b,A,B can also be read as a,b,c,d.
    re = poly_add(poly_mul(a, A), poly_mul(b, B), -1)
    im = poly_add(poly_mul(a, B), poly_mul(b, A))
    norm_product = poly_add(poly_mul(re, re), poly_mul(im, im))
    norm_a = poly_add(poly_mul(a, a), poly_mul(b, b))
    norm_b = poly_add(poly_mul(A, A), poly_mul(B, B))
    norm_residual = poly_add(norm_product, poly_mul(norm_a, norm_b), -1)
    check(not norm_residual, "Universal complex norm identity failed")
    return 2


def verify_inverse(order: int) -> tuple[int, list[int]]:
    # g(t) = sum_{n>=1} (-1)^(n-1) Catalan(n-1) t^n.
    g: Laurent = {
        n: Fraction((-1) ** (n - 1) * (comb(2 * n - 2, n - 1) // n))
        for n in range(1, order + 1)
    }
    identity: Laurent = {1: Fraction(1)}
    phi_of_g = truncate(laurent_add(g, laurent_mul(g, g, order)), order)
    check(phi_of_g == identity, "phi(g(t)) = t failed")
    g_of_phi = substitute_phi(g, order)
    check(g_of_phi == identity, "g(phi(t)) = t failed")
    return 2, [int(g[n]) for n in range(1, min(8, order) + 1)]


def random_laurent(rng: random.Random) -> Laurent:
    out: Laurent = {}
    for n in range(-5, 6):
        c = Fraction(rng.randrange(-5, 6), rng.randrange(1, 6))
        if c and rng.randrange(3) != 0:
            out[n] = c
    return out


def verify_random(seed: int, samples: int, cutoff: int) -> dict[str, int]:
    rng = random.Random(seed)
    counters = {
        "substitution_additivity": 0,
        "substitution_multiplicativity": 0,
        "leading_term_preservation": 0,
        "derivation_leibniz": 0,
        "derivation_valuation_gain": 0,
        "ordered_witness_arithmetic": 0,
    }
    for _ in range(samples):
        a, b = random_laurent(rng), random_laurent(rng)
        sa = substitute_phi(a, cutoff)
        sb = substitute_phi(b, cutoff)
        check(substitute_phi(laurent_add(a, b), cutoff) == laurent_add(sa, sb),
              "Substitution additivity failed")
        counters["substitution_additivity"] += 1

        # Guard digits: negative powers in the OTHER factor can lower the
        # exponent. Expanding only through cutoff in both factors is unsound.
        low_a, low_b = min(a, default=0), min(b, default=0)
        sa_guard = substitute_phi(a, cutoff - min(0, low_b))
        sb_guard = substitute_phi(b, cutoff - min(0, low_a))
        lhs = substitute_phi(laurent_mul(a, b), cutoff)
        rhs = laurent_mul(sa_guard, sb_guard, cutoff)
        check(lhs == rhs, "Guarded substitution multiplicativity failed")
        counters["substitution_multiplicativity"] += 1

        if a:
            check(valuation(a) == valuation(sa), "Valuation preservation failed")
            check(a[min(a)] == sa[min(sa)], "Leading coefficient changed")
        else:
            check(not sa, "Zero substitution failed")
        counters["leading_term_preservation"] += 1

        dab = derivative(laurent_mul(a, b))
        rhs_d = laurent_add(laurent_mul(derivative(a), b),
                           laurent_mul(a, derivative(b)))
        check(dab == rhs_d, "Leibniz identity failed")
        counters["derivation_leibniz"] += 1
        da = derivative(a)
        if a and da:
            check(min(da) >= min(a) + 1, "D valuation gain failed")
        counters["derivation_valuation_gain"] += 1

        A = Fraction(rng.randrange(-100, 101), rng.randrange(1, 15))
        delta = Fraction(rng.choice([n for n in range(-30, 31) if n]),
                         rng.randrange(1, 15))
        H = Fraction(rng.randrange(1, 101), rng.randrange(1, 15))
        witness = 2 * H * (1 + abs(A)) / delta
        check(abs(witness * delta) == 2 * H * (1 + abs(A)),
              "Ordered witness formula failed")
        check(abs(witness * delta) > H * (1 + abs(A)),
              "Ordered witness strict bound failed")
        counters["ordered_witness_arithmetic"] += 1
    return counters


def verify_displacements(max_m: int) -> tuple[int, list[dict[str, int]]]:
    examples: list[dict[str, int]] = []
    for m in range(1, max_m + 1):
        monomial: Laurent = {-m: Fraction(1)}
        diff = laurent_add(substitute_phi(monomial, -m + 8),
                           scale(monomial, Fraction(-1)))
        check(valuation(diff) == 1 - m, "Displacement valuation formula failed")
        check(diff[1 - m] == -m, "Displacement leading coefficient failed")
        if m <= 8:
            examples.append({"m": m, "valuation": min(diff),
                             "leading_coefficient": int(diff[min(diff)])})
    return max_m, examples


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: optimized Python mode is rejected.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "verification.json")
    parser.add_argument("--seed", type=int, default=20260922)
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--order", type=int, default=48)
    args = parser.parse_args()
    if args.samples < 1 or args.order < 8:
        parser.error("--samples must be positive and --order must be at least 8")

    n_universal = verify_universal_identities()
    n_inverse, inverse_coeffs = verify_inverse(args.order)
    n_displacement, examples = verify_displacements(128)
    randomized = verify_random(args.seed, args.samples, cutoff=12)
    result = {
        "status": "PASS",
        "scope": "Exact finite identities and Laurent-series examples only; not a formal surreal proof.",
        "python_version": platform.python_version(),
        "external_dependencies": [],
        "seed": args.seed,
        "random_samples": args.samples,
        "inverse_series_order": args.order,
        "universal_polynomial_identities": n_universal,
        "inverse_composition_checks": n_inverse,
        "displacement_formula_checks": n_displacement,
        "randomized_checks": randomized,
        "total_named_checks": n_universal + n_inverse + n_displacement + sum(randomized.values()),
        "inverse_first_coefficients": inverse_coeffs,
        "displacement_examples": examples,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, RuntimeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
