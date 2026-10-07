#!/usr/bin/env python3
"""Exact arithmetic certificate for the ordinary-sensitivity companion.

Only the Python standard library is used.  No floating-point operation enters
the certificate.  This verifies the integer consequences of the combinatorial
recurrences proved in article.tex, not the enormous Boolean truth table.
Every check remains active when Python is run with optimization enabled.

Usage:
    python verify.py
    python verify.py --json certificate.json
"""
import argparse
import json
from math import comb, prod
from pathlib import Path

EXPONENTS = [
    43, 43, 39, 39, 40, 40, 37, 36, 34, 32,
    30, 28, 26, 24, 23, 22, 20, 19, 18, 15,
]
DEPTH = 20
BASE_BLOCKS = 2**18
COPIES = 100
POSITIONS = 4
S_STAR = 9 * 2**318
B_STAR = 100 * 2**646


def require(condition, message):
    """Enforce a certificate condition, including under python -O."""
    if not condition:
        raise ArithmeticError(message)


def verify():
    require(len(EXPONENTS) == DEPTH, "The exponent schedule must have twenty levels.")
    require(sum(EXPONENTS) == 608, "The outdegree exponents must sum to 608.")
    block_size = DEPTH + 2
    # List entry q-1 is the envelope for predicate q (one-based in the paper).
    a = [block_size - q for q in range(1, DEPTH + 2)]
    c = [block_size * BASE_BLOCKS - DEPTH - 1 + q
         for q in range(1, DEPTH + 2)]
    u = v = 0
    stages = []

    for level, e in enumerate(EXPONENTS, start=1):
        h, tau = 2**e, e + 6
        k = 2 * h + 1
        # The labelling union bound is less than 2**(-tau).
        require(
            k**tau * POSITIONS**tau * 2**tau < POSITIONS**comb(tau, 2),
            f"The label-existence inequality failed at level {level}.",
        )
        H = len(a) - 1
        require(H == DEPTH + 1 - level,
                f"The input profile length is inconsistent at level {level}.")
        new_a = [
            (tau - 1) * a[-1] + max(c[H - q] + v, 3 * v)
            for q in range(1, H + 1)
        ]
        new_c = [
            h * a[H - q] + POSITIONS * c[-1]
            for q in range(1, H + 1)
        ]
        new_u = (tau - 1) * a[-1] + 3 * v
        new_v = h * u + POSITIONS * c[-1]
        a, c, u, v = new_a, new_c, new_u, new_v
        require(len(a) == len(c) == H,
                f"The output profile lengths are inconsistent at level {level}.")
        stages.append({
            "level": level, "outdegree_exponent": e, "exclusion_threshold": tau,
            "A": a, "C": c, "U": u, "V": v,
        })

    require(len(a) == len(c) == 1, "Each final profile must have one entry.")
    exact_sensitivity_envelope = max(COPIES * a[0], c[0])
    require(COPIES * a[0] < S_STAR,
            "The zero-sensitivity bound must be less than S_star.")
    require(c[0] < S_STAR, "The one-sensitivity bound must be less than S_star.")
    ks = [2**(e + 1) + 1 for e in EXPONENTS]
    sensitive_blocks = COPIES * BASE_BLOCKS * prod(ks)
    require(sensitive_blocks > B_STAR, "The block count must exceed B_star.")

    seed_dimension = COPIES * block_size * BASE_BLOCKS * POSITIONS**DEPTH * prod(ks)
    require(seed_dimension == sensitive_blocks * block_size * POSITIONS**DEPTH,
            "The seed dimension is inconsistent with the sensitive blocks.")

    # Exact rational exponent certificate.  This also checks its short reduction.
    require(32 * 646 - 65 * 318 == 2, "The power-of-two cancellation failed.")
    require(B_STAR**32 > S_STAR**65, "The certified exponent must exceed 65/32.")
    require(4 * 100**32 > 9**65, "The reduced exponent inequality failed.")
    require(2 * 100**3 > 3 * 81**3, "The elementary exponent comparison failed.")
    return {
        "result": "PASS",
        "depth": DEPTH,
        "base_blocks": BASE_BLOCKS,
        "copies": COPIES,
        "positions_per_row": POSITIONS,
        "outdegree_exponents": EXPONENTS,
        "A_final": a[0],
        "C_final": c[0],
        "exact_sensitivity_envelope": exact_sensitivity_envelope,
        "S_star": S_STAR,
        "B_star": B_STAR,
        "sensitive_blocks": sensitive_blocks,
        "seed_dimension": seed_dimension,
        "rational_exponent": {"numerator": 65, "denominator": 32},
        "exact_inequality": "B_star**32 > S_star**65",
        "stages": stages,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write every exact profile to this file")
    args = parser.parse_args()
    certificate = verify()
    print("PASS: all twenty label-existence inequalities hold exactly.")
    print("PASS: 100*A_final < 9*2**318 and C_final < 9*2**318.")
    print("PASS: the disjoint-block count exceeds 100*2**646.")
    print("PASS: B_star**32 > S_star**65.")
    print("A_final =", certificate["A_final"])
    print("C_final =", certificate["C_final"])
    if args.json is not None:
        args.json.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
        print("Exact profile certificate written to", args.json)


if __name__ == "__main__":
    main()
