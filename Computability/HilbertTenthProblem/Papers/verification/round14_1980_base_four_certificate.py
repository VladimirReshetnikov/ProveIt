#!/usr/bin/env python3
"""106 operations: store a0=A-4 and use the base-four exponent congruence.

The supplied positive input a now denotes a0=M(U+1); the mathematical
main Pell parameter is A=a+4.  The E14 congruence is for bw=4^(2r+1).
Its coefficient A-4 is already a, while A-B=a-(B-4) shares the third
mask register.  MAIN_PELL_BASE_FOUR_PROOF.md supplies the new ratio and
positive-domain argument; no assertion of a free affine computation is used.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round13_1980_certificate as previous

HERE = Path(__file__).resolve().parent
OUT = HERE / "round14_1980_base_four_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    replacement = {
        "cam2": ("cam2", "*", "c", "a"),
        "am1": ("am1", "+", "a", 3),
        "ap1": ("ap1", "+", "am1", 2),
        "a4": ("a4", "*", 8, "a"),
        "a4m5": ("a4m5", "+", "a4", 15),
        "amb": ("amb", "-", "a", "b5m2"),
    }
    schedule = [replacement.get(row[0], row) for row in previous.SCHEDULE
                if row[0] != "am2"]
    baseline.need(len(schedule) == 106, "one main-parameter subtraction is eliminated")
    return schedule


SCHEDULE = make_schedule()
NUMERAL_SCHEDULE = list(previous.NUMERAL_SCHEDULE) + [
    ("lit_three", "+", "lit_two", 1),
    ("lit_eight", "+", "lit_four", "lit_four"),
    ("lit_fifteen", "-", "lit_16", 1),
]
LITERAL_REGISTERS = dict(previous.LITERAL_REGISTERS) | {
    3: "lit_three", 8: "lit_eight", 15: "lit_fifteen",
}
STRICT_SCHEDULE = NUMERAL_SCHEDULE + [
    (target, operation, LITERAL_REGISTERS.get(left, left),
     LITERAL_REGISTERS.get(right, right))
    for target, operation, left, right in SCHEDULE
]


def source_residuals():
    s = SYM
    # Change the mathematical Pell parameter throughout the source system,
    # then retain the defining equation for its supplied coordinate a0.
    source = [res.subs(s["a"], s["a"] + 4)
              for res in previous.source_residuals()]
    source[11] = previous.source_residuals()[11]
    A = s["a"] + 4
    source[13] = s["d"] - s["b"]*s["w"] - s["c"]*(A - 4) \
        - s["ga"]*(8*A - 17)
    return source


def verify_certificate():
    receipt = previous.verify_certificate()
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
    primitives, primitive_histogram = previous.verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 106 and primitive_histogram == {"+": 47, "*": 59},
                  "106-operation core histogram")
    numeral_env = {}
    numeral_histogram = baseline.run_schedule(NUMERAL_SCHEDULE, numeral_env)
    for value, register in LITERAL_REGISTERS.items():
        baseline.need(numeral_env[register] == value, "all fixed numerals are constructed")
    numeral_primitives, _ = previous.verify_primitives(NUMERAL_SCHEDULE, numeral_env)
    strict_env = dict(SYM)
    strict_histogram = baseline.run_schedule(STRICT_SCHEDULE, strict_env)
    strict_primitives, strict_primitive_histogram = previous.verify_primitives(STRICT_SCHEDULE, strict_env)
    baseline.need(len(strict_primitives) == 115 and
                  strict_primitive_histogram == {"+": 51, "*": 64}, "explicit 115-operation strict certificate")
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
        "residual_polynomials": records,
        "reparameterized_inputs": receipt["reparameterized_inputs"] | {
            "a": "positive a0=R*Y*(U+1), mathematical main Pell parameter A=a0+4",
            "w": "the base-four exponent congruence forces b*w=4^(2*r+1)",
        },
        "numerals_from_one": {"operations": 9, "histogram": numeral_histogram,
            "primitive_instructions": numeral_primitives,
            "scope": "Generate2,3,4,8,15,L from1; x,Z,V,H remain supplied parameters"},
        "operations_with_numerals_from_one": 115,
        "strict_certificate": {"operations": 115, "straight_line_histogram": strict_histogram,
            "additions_and_multiplications_only": {"additions": 51, "multiplications": 64},
            "primitive_instructions": strict_primitives, "equalities": EQUALITIES,
            "only_literal": 1},
        "proofs": receipt["proofs"] + ["../1980/MAIN_PELL_BASE_FOUR_PROOF.md"],
        "scope": "106 core operations by a shifted main Pell parameter and base-four exponent congruence; explicit strict certificate115 is not an improvement over the separate113 milestone",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"],
          ";", result["operations_with_numerals_from_one"], "with numerals from1;")
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
