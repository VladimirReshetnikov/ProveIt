#!/usr/bin/env python3
"""Exact finite checks for Period Arithmetic and Noncanonical Surcomplex Exponentials.

No external dependencies. These tests do not verify the transfinite existence
proofs, arbitrary Hahn supports, or mathematical novelty.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
from typing import Dict
import json


def alpha_residue(n: int) -> int:
    """Residue of the profinite element with 2-component 0, odd components 1."""
    if n <= 0:
        raise ValueError("The modulus must be positive.")
    odd, two = n, 1
    while odd % 2 == 0:
        odd //= 2
        two *= 2
    if odd == 1:
        return 0
    # a = two*k and a == 1 (mod odd); two is invertible modulo odd.
    return (two * pow(two, -1, odd)) % n


def mod_one(x: Fraction) -> Fraction:
    return x - x.numerator // x.denominator


def character(x: Fraction) -> Fraction:
    """Return a rational turn in [0,1), not a floating complex phase."""
    return mod_one(Fraction(x.numerator * alpha_residue(x.denominator),
                            x.denominator))


def binomial(a: Fraction, n: int) -> Fraction:
    if n < 0:
        raise ValueError("Degree must be nonnegative.")
    out = Fraction(1)
    for j in range(n):
        out *= (a - j) / (j + 1)
    return out


Polynomial = Dict[int, Fraction]


def multiply(a: Polynomial, b: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for i, ai in a.items():
        for j, bj in b.items():
            out[i + j] = out.get(i + j, Fraction(0)) + ai * bj
    return {i: value for i, value in out.items() if value}


def explicit_phase(poly: Polynomial) -> Fraction:
    # Only the X-coefficient is used by h; the constant is a finite turn.
    return mod_one(character(poly.get(1, Fraction(0)))
                   + poly.get(0, Fraction(0)))


def run_checks() -> dict:
    counts = {}
    residues = {n: alpha_residue(n) for n in range(1, 129)}
    crt_count = 0
    for n, residue in residues.items():
        odd, two = n, 1
        while odd % 2 == 0:
            odd //= 2
            two *= 2
        assert 0 <= residue < n
        assert residue % two == 0
        assert (residue - 1) % odd == 0
        crt_count += 1
    counts["crt_moduli"] = crt_count

    compat = 0
    for n in range(1, 129):
        for m in range(n, 129, n):
            assert residues[m] % n == residues[n]
            compat += 1
    counts["residue_compatibility_pairs"] = compat

    rationals = sorted({Fraction(k, n) for n in range(1, 17)
                        for k in range(-12, 13)})
    additivity = 0
    for x in rationals:
        for y in rationals:
            assert character(x + y) == mod_one(character(x) + character(y))
            additivity += 1
    counts["rational_grid_size"] = len(rationals)
    counts["character_additivity_pairs"] = additivity

    X = {1: Fraction(1)}
    u = {1: Fraction(1, 3), 0: Fraction(-1, 3)}
    product = multiply(X, u)
    assert explicit_phase(X) == 0
    assert explicit_phase(u) == 0
    assert explicit_phase(product) == Fraction(2, 3)
    assert character(Fraction(1, 3)) == Fraction(1, 3)
    for e in range(11):
        assert character(Fraction(1, 2**e)) == 0
    counts["displayed_example_assertions"] = 15

    q_values = [Fraction(-3), Fraction(-1), Fraction(-1, 2),
                Fraction(0), Fraction(1, 3), Fraction(1), Fraction(5, 2)]
    c_values = [Fraction(-2), Fraction(-1, 2), Fraction(0),
                Fraction(1, 3), Fraction(2)]
    composition = 0
    for q in q_values:
        for c in c_values:
            for d in c_values:
                for degree in range(9):
                    lhs = sum((binomial(-q, n) * d**n
                               * binomial(-(q + n), degree - n)
                               * c**(degree - n)
                               for n in range(degree + 1)), Fraction(0))
                    rhs = binomial(-q, degree) * (c + d)**degree
                    assert lhs == rhs, (q, c, d, degree, lhs, rhs)
                    composition += 1
    counts["translation_composition_coefficients"] = composition

    # Witnesses of the one-step construction for h=0 and finite polynomials.
    # L(f)=([X^D]f / [X^D]y)*t on the span tested below. Since D>deg(p),
    # this assigns L(p)=0 and L(y)=t exactly.
    polynomials = [
        {1: Fraction(1)},
        {2: Fraction(1), 0: Fraction(1)},
        {3: Fraction(2), 1: Fraction(-5), 0: Fraction(7, 3)},
        {5: Fraction(1, 3), 4: Fraction(-2), 2: Fraction(5)},
    ]
    witness_data = []
    for a in polynomials:
        for g in range(1, 7):
            p = {g: Fraction(1)}
            y = multiply(a, p)
            degree = max(y)
            assert degree > g and 0 not in y
            lp = p.get(degree, Fraction(0)) / y[degree]
            ly = y[degree] / y[degree]
            assert lp == 0 and ly == 1
            # First coefficient of Exp(2*pi*i*t)-1 is nonzero. Removing
            # its fixed scalar, the exact infinitesimal angle coordinate is 1.
            witness_data.append({"a_degree": max(a), "p_degree": g,
                                 "product_degree": degree,
                                 "L_p_t_coefficient": str(lp),
                                 "L_product_t_coefficient": str(ly)})
    counts["one_step_multiplier_witnesses"] = len(witness_data)

    # Constant-term shadows under X -> X-c for rational polynomials.
    shadow_checks = 0
    for polynomial in polynomials:
        for c in c_values:
            evaluated = sum((ai * (-c)**i for i, ai in polynomial.items()),
                            Fraction(0))
            expanded_constant = sum((ai * binomial(Fraction(i), i)
                                     * (-c)**i for i, ai in polynomial.items()),
                                    Fraction(0))
            assert evaluated == expanded_constant
            shadow_checks += 1
    counts["constant_term_shadow_checks"] = shadow_checks

    return {
        "status": "PASS",
        "arithmetic": "exact fractions; no numerical approximations",
        "scope": "finite identities and examples only; no transfinite or Lean verification",
        "counts": counts,
        "selected_profinite_residues": {str(n): residues[n]
                                       for n in (2, 3, 6, 12, 24, 40, 60, 120)},
        "nonring_example_turns": {"X": "0", "(X-1)/3": "0",
                                  "X*(X-1)/3": "2/3"},
        "multiplier_witnesses": witness_data,
    }


def main() -> None:
    report = run_checks()
    destination = Path(__file__).resolve().with_name("verification.json")
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "counts": report["counts"]}, indent=2))
    print(f"Wrote {destination}")


if __name__ == "__main__":
    main()
