#!/usr/bin/env python3
"""106 core operations, or 114 when all fixed numerals are generated from 1.

Keep the round14 base-four Pell system, but calculate A+1=a0+5 before
A-1=(A+1)-2 and calculate its exponent modulus as 8*(A+1)-25.
The modular Sidon layout is unchanged; its exponent is enlarged to 5**16.
BASE_FOUR_NUMERAL_VARIANT_PROOF.md supplies the exact accounting and index.
The independent 107-core / 113-strict certificate is preserved unchanged.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round13_1980_certificate as layout
import round14_1980_base_four_certificate as previous

HERE = Path(__file__).resolve().parent
OUT = HERE / "round15_1980_certificate.json"
L, K = 5**16, layout.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "am1":
            baseline.need((operation, left, right) == ("+", "a", 3),
                          "the predecessor's A-1 calculation is replaced")
            schedule.append(("ap1", "+", "a", 5))
            schedule.append(("am1", "-", "ap1", 2))
            continue
        if target == "ap1":
            baseline.need((operation, left, right) == ("+", "am1", 2),
                          "the predecessor's A+1 calculation is moved, not copied")
            continue
        if target == "a4":
            baseline.need((operation, left, right) == ("*", 8, "a"),
                          "the old exponent-modulus product")
            right = "ap1"
        if target == "a4m5":
            baseline.need((operation, left, right) == ("+", "a4", 15),
                          "the old exponent-modulus addition")
            operation, right = "-", 25
        if target == "R20":
            baseline.need(right == previous.L, "only the fixed exponent changes")
            right = L
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 106, "the core count is unchanged")
    return schedule


SCHEDULE = make_schedule()
NUMERAL_SCHEDULE = [
    ("lit_two", "+", 1, 1),
    ("lit_four", "*", "lit_two", "lit_two"),
    ("lit_five", "+", "lit_four", 1),
    ("lit_eight", "+", "lit_four", "lit_four"),
    ("lit_25", "*", "lit_five", "lit_five"),
    ("lit_625", "*", "lit_25", "lit_25"),
    ("lit_390625", "*", "lit_625", "lit_625"),
    ("lit_exponent", "*", "lit_390625", "lit_390625"),
]
LITERAL_REGISTERS = {2: "lit_two", 4: "lit_four", 5: "lit_five",
                     8: "lit_eight", 25: "lit_25", L: "lit_exponent"}
STRICT_SCHEDULE = NUMERAL_SCHEDULE + [
    (target, operation, LITERAL_REGISTERS.get(left, left),
     LITERAL_REGISTERS.get(right, right))
    for target, operation, left, right in SCHEDULE
]


def source_residuals():
    source = list(previous.source_residuals())
    baseline.need(EQUATION_LABELS[19] == "E20", "fixed exponent equation position")
    source[19] = SYM["ka"] - L - SYM["Delta"]*(SYM["a"] + 3)
    return source


def verify_support_bounds():
    support = dict(layout.verify_support_bounds())
    baseline.need(3*K + 2 == 950157215 < L == 152587890625,
                  "the enlarged exponent satisfies every degree margin")
    baseline.need(L > layout.L and L >= 2, "the new exponent is a valid enlargement")
    support["exponent"] = str(L)
    return support


def verify_certificate():
    receipt = previous.verify_certificate()
    support = verify_support_bounds()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A = s["a"] + 4
    G_source = 1 + (A + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (A + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**2*(s["n"]**2 - 1),
        16: source[15]*(A + 1)*(G_source + G_calculated)*H17**2,
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 equality tests")
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual - residual - correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual + residual) == 0:
            sign = -1
        else:
            raise AssertionError(f"residual mismatch at {EQUATION_LABELS[index]}")
        records.append({"equation": EQUATION_LABELS[index], "equality": [left, right],
                        "source_residual_polynomial": sp.sstr(sp.expand(residual)),
                        "certificate_residual_polynomial": sp.sstr(actual),
                        "source_residual_sign": sign,
                        "triangular_correction_polynomial": sp.sstr(sp.expand(correction))})
    for name, expected in {
        "am1": A - 1, "ap1": A + 1, "A": A*A - 1,
        "a4m5": 8*A - 17, "amb": A - env["B"],
        "cam2": s["c"]*(A - 4),
    }.items():
        baseline.need(sp.expand(env[name] - expected) == 0, "exact shifted register " + name)
    primitives, primitive_histogram = layout.verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 106 and primitive_histogram == {"+": 47, "*": 59},
                  "106-operation core histogram")
    literals = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
                if isinstance(operand, int)}
    baseline.need(literals == {1, 2, 4, 5, 8, 25, L}, "the exact required literal set")
    numeral_env = {}
    numeral_histogram = baseline.run_schedule(NUMERAL_SCHEDULE, numeral_env)
    for value, register in LITERAL_REGISTERS.items():
        baseline.need(numeral_env[register] == value, "all fixed numerals are constructed")
    numeral_primitives, numeral_primitive_histogram = layout.verify_primitives(
        NUMERAL_SCHEDULE, numeral_env)
    baseline.need(len(numeral_primitives) == 8 and
                  numeral_primitive_histogram == {"+": 3, "*": 5}, "eight numeral operations")
    strict_env = dict(SYM)
    strict_histogram = baseline.run_schedule(STRICT_SCHEDULE, strict_env)
    strict_primitives, strict_primitive_histogram = layout.verify_primitives(STRICT_SCHEDULE, strict_env)
    baseline.need(len(strict_primitives) == 114 and
                  strict_primitive_histogram == {"+": 50, "*": 64}, "explicit strict114 certificate")
    baseline.need({operand for _, _, left, right in STRICT_SCHEDULE
                   for operand in (left, right) if isinstance(operand, int)} == {1},
                  "strict instructions only use the literal one")
    for name in env:
        baseline.need(sp.expand(strict_env[name] - env[name]) == 0,
                      "strict and core values agree exactly")
    receipt.update({
        "operations": 106, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 47, "multiplications": 59},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": support,
        "exponent_numeral": str(L),
        "numerals_from_one": {"operations": 8, "histogram": numeral_histogram,
            "primitive_instructions": numeral_primitives,
            "scope": "Generate 2,4,5,8,25,L from 1; x,Z,V,H remain supplied parameters"},
        "operations_with_numerals_from_one": 114,
        "strict_certificate": {"operations": 114, "straight_line_histogram": strict_histogram,
            "additions_and_multiplications_only": {"additions": 50, "multiplications": 64},
            "primitive_instructions": strict_primitives, "equalities": EQUALITIES,
            "only_literal": 1},
        "proofs": receipt["proofs"] + ["../1980/BASE_FOUR_NUMERAL_VARIANT_PROOF.md"],
        "scope": "106 core operations for the base-four system with the enlarged modular Sidon exponent; explicit strict114 does not improve the separate strict113 certificate",
        "fixed_index_override": "BASE_FOUR_NUMERAL_VARIANT_PROOF.md preserves the modular Sidon variable weights, row weights and K, replaces L by 5^16, and rebuilds V and H for that L",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"],
          ";", result["operations_with_numerals_from_one"], "with numerals from 1")
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
    print("Support:", K, L)
