#!/usr/bin/env python3
"""Finite arithmetic diagnostics for the local coded-powers proof.

These checks test rounding, finite scale inequalities, local domain bounds,
small concrete beta codes, and the anchored cancellation identity. They do
not test uncountability, nonstandard models, infinite fusion, or ATR_0.
Uses only the Python standard library. Run with an optional JSON output path.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
import random
import sys


SEED = 20261004
RNG = random.Random(SEED)
COUNTS: dict[str, int] = {}


def check(condition: bool, group: str, description: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {description}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def crt_code(values: list[int], multiplier: int) -> tuple[int, int]:
    """One standard finite Goedel beta code, constructed explicitly by CRT."""
    length = len(values) - 1
    v = multiplier * math.factorial(length + 1) * (max(values) + 1)
    moduli = [1 + (i + 1) * v for i in range(length + 1)]
    for i, modulus in enumerate(moduli):
        for earlier in moduli[:i]:
            check(math.gcd(modulus, earlier) == 1, "beta", "coprime moduli")
    product = math.prod(moduli)
    u = sum(
        value * (product // modulus) * pow(product // modulus, -1, modulus)
        for value, modulus in zip(values, moduli)
    ) % product
    return u, v


def beta(u: int, v: int, index: int) -> int:
    return u % (1 + (index + 1) * v)


def diagnose_beta() -> dict[str, object]:
    cases = 0
    max_code_bits = 0
    for base in (2, 3, 5, 7):
        for length in (0, 1, 2, 4, 7, 9):
            values = [base**i for i in range(length + 1)]
            first = crt_code(values, 1)
            second = crt_code(values, 2)
            max_code_bits = max(max_code_bits, first[0].bit_length(), second[0].bit_length())
            for index, expected in enumerate(values):
                observed = beta(*first, index)
                check(observed == expected, "beta", "CRT decoding")
                check(observed == beta(*second, index), "beta", "two valid codes agree")
                check(observed <= first[0], "beta", "remainder bounded by code")
                if index < length:
                    check(beta(*first, index + 1) == base * observed, "beta", "recurrence")
                    check(beta(*first, index + 1) > observed, "beta", "strict growth")
                for other in range(length + 1 - index):
                    check(
                        beta(*first, index + other)
                        == observed * beta(*first, other),
                        "beta",
                        "local homomorphism within the code bound",
                    )
            cases += 1
    return {"cases": cases, "bases": [2, 3, 5, 7], "maximum_length": 9,
            "largest_code_bit_length": max_code_bits}


def diagnose_scales() -> dict[str, object]:
    cases = 0
    depths: list[int] = []
    vertex_checks = 0
    large_anchor_cases = 0
    largest_anchor_bits = 0
    for bits in (512, 1024, 2048, 4096):
        for irregular in (False, True):
            c = (1 << bits) + (RNG.getrandbits(bits - 1) if irregular else 0)
            for rounding in (0, 2 * c, RNG.randrange(2 * c + 1)):
                width = c * c + rounding
                b = 0 if cases % 3 == 0 else (7 * width + 5 if cases % 3 == 1 else width**3 + 17)
                d = b + width
                largest_anchor_bits = max(largest_anchor_bits, b.bit_length())
                large_anchor_cases += int(b > width)
                check(math.isqrt(width) == c, "scales", "floor square root at boundary")
                check(c * c <= width < (c + 1) ** 2, "scales", "root bracketing")

                t = [c]
                for _ in range(13):
                    t.append(math.isqrt(t[-1]))
                depth = min(8, sum(1 for n in range(8) if t[n + 3] > 8))
                depths.append(depth)
                check(depth >= 1, "scales", "finite usable scale window")
                s = [c // value for value in t[:depth + 2]]
                for n in range(depth + 1):
                    check(t[n + 1] ** 2 <= t[n] < (t[n + 1] + 1) ** 2,
                          "scales", "iterated exact roots")
                    check(s[n] * t[n] <= c < (s[n] + 1) * t[n],
                          "scales", "exact quotient bracket")
                for n in range(depth):
                    check(s[n + 1] >= s[n] * t[n + 1], "scales", "first scale inequality")
                    check(s[n] * t[n + 1] >= s[n] * t[n + 2] ** 2,
                          "scales", "second scale inequality")
                    check(s[n + 1] > 8 * s[n] * t[n + 2],
                          "scales", "strict factor-eight separation")

                selected: list[int] = []
                partial_sums = [0]
                for n in range(depth):
                    grid_length = t[n + 3]
                    start = RNG.randrange(grid_length - 1)
                    difference = RNG.randrange(1, grid_length - start)
                    x = s[n + 1] * start
                    h = s[n + 1] * difference
                    check(0 <= x < x + h < c, "buffers", "two points in one bounded grid")
                    check(s[n + 1] <= h < s[n + 1] * grid_length < c,
                          "buffers", "perturbation interval")
                    if selected:
                        check(h > 8 * selected[-1], "buffers", "arbitrary selected scales separate")
                    check(n + 3 < c, "buffers", "finite-stage numeral below local buffer")
                    for subtotal in partial_sums:
                        m = b + 2 * c + subtotal
                        check(b <= m - x <= d, "buffers", "continuity multiplier stays in interval")
                        check(m + h < b + (n + 3) * c < b + c * c <= d,
                              "buffers", "new exponent stays within local code")
                        check(b <= b + h <= d, "buffers", "anchored multiplier stays in interval")
                        check((m - x) + (x + h) == m + h,
                              "buffers", "local transfer indices agree")
                        vertex_checks += 1
                    partial_sums += [subtotal + h for subtotal in partial_sums]
                    check(len(set(partial_sums)) == len(partial_sums),
                          "buffers", "finite vertices have distinct exponent sums")
                    selected.append(h)
                cases += 1
    return {"cases": cases, "c_bit_parameters": [512, 1024, 2048, 4096],
            "minimum_finite_depth": min(depths), "maximum_finite_depth": max(depths),
            "finite_vertex_checks": vertex_checks,
            "cases_with_anchor_larger_than_local_width": large_anchor_cases,
            "largest_anchor_bit_length": largest_anchor_bits}


def diagnose_anchor() -> dict[str, object]:
    cases = 0
    cases_combined_index_exceeds_code = 0
    for base in (2, 3, 5):
        for b in (0, 10, 1000, 10000):
            for width in (100, 121, 250):
                c = math.isqrt(width)
                d = b + width
                h = RNG.randrange(1, c)
                x = RNG.randrange(c)
                m = b + 2 * c + RNG.randrange(c)
                needed = {b, b + h, m, m + h, m - x, x, x + h}
                check(all(0 <= index <= d for index in needed),
                      "anchor", "only legal local indices evaluated")
                local = {index: base**index for index in needed}
                left = local[b] * local[m + h]
                right = local[b + h] * local[m]
                check(left == right, "anchor", "anchored finite equality")
                check(local[m - x] * local[x + h] == local[m + h],
                      "anchor", "local transfer identity")
                check(local[m + h] == (base**h) * local[m],
                      "anchor", "cancelled finite flip identity")
                check(left // local[b] == local[m + h], "anchor", "positive factor cancellation")
                cases_combined_index_exceeds_code += int(b + m + h > d)
                cases += 1
    check(cases_combined_index_exceeds_code > 0, "anchor",
          "exercise products whose combined exponent is outside the local interval")
    return {"cases": cases,
            "cases_with_combined_product_index_outside_code": cases_combined_index_exceeds_code,
            "maximum_anchor": 10000,
            "interpretation": "Products use only separately valid local values; no out-of-domain E evaluation."}


def main() -> None:
    result = {
        "status": "passed",
        "seed": SEED,
        "scope": "Finite diagnostics of explicit arithmetic identities and integer bounds.",
        "not_tested": ["nonstandard models", "external uncountability", "infinite fusion",
                       "Borel regularization", "ATR_0 provability"],
        "beta_codes": diagnose_beta(),
        "integer_scales_and_buffers": diagnose_scales(),
        "anchored_identities": diagnose_anchor(),
    }
    result["assertions_by_group"] = COUNTS
    result["total_assertions"] = sum(COUNTS.values())
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("local_arithmetic_diagnostics.json")
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
