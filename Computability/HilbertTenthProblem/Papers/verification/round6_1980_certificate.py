#!/usr/bin/env python3
"""Compose the direct quadratic encoding and shifted auxiliary Pell parameter.

This preserves every earlier certificate. The new scheme uses 112 arithmetic
checks and 20 equality tests, with 32 positive system unknowns. Symbolic
verification certifies its arithmetic; the accompanying mathematical proofs
establish the fixed-index encoding and positive-domain equivalences.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round6_1980_quadratic_certificate as quadratic
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round6_1980_certificate.json"
L = quadratic.L
PARAMETERS = list(quadratic.PARAMETERS)
NAMES = [name for name in quadratic.NAMES if name != "p"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(quadratic.EQUALITIES)
EQUATION_LABELS = list(quadratic.EQUATION_LABELS)
baseline.need(EQUALITIES[7] == ("p", "R8") and EQUATION_LABELS[7] == "E8",
              "explicit parameter equation to eliminate")
del EQUALITIES[7]
del EQUATION_LABELS[7]


def make_schedule():
    schedule = list(quadratic.SCHEDULE)
    replace_block(schedule, ["p2", "p2m1"], [
        ("Pplus1", "+", "R8", 2),
        ("p2m1", "*", "R8", "Pplus1"),
    ])
    baseline.need([row for row in schedule if row[0] == "pm1"]
                  == [("pm1", "-", "p", 1)], "unique old p-1 computation")
    schedule = [row for row in schedule if row[0] != "pm1"]
    schedule = [(target, operation,
                 "R8" if left == "pm1" else left,
                 "R8" if right == "pm1" else right)
                for target, operation, left, right in schedule]
    baseline.need(len(schedule) == 112, "composed schedule length")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    X = 2*s["w"]*s["s"]**2*s["r"]**2*s["n"]**6
    source = [res.subs(quadratic.SYM["p"], X + 1)
              for res in quadratic.source_residuals()]
    del source[7]
    return source


def verify_certificate():
    support = quadratic.verify_support_bounds()
    baseline.need(len(NAMES) == len(set(NAMES)) == 36, "36 distinct positive inputs")
    baseline.need(len(set(NAMES) - set(PARAMETERS)) == 32, "32 positive unknowns")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]*(s["n"]**2 - 1),
        16: source[15]*(s["a"] + 1)*(G_source + G_calculated)*H17**2,
    }
    baseline.need(len(source) == len(EQUALITIES) == len(EQUATION_LABELS) == 20,
                  "20 explicit source equations and tests")
    records = []
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
    primitives = primitive_instructions(SCHEDULE)
    primitive_histogram = {"+": 0, "*": 0}
    for instruction in primitives:
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right, target = (value(instruction[name]) for name in ["left", "right", "result"])
        operation = instruction["operation"]
        baseline.need(operation in primitive_histogram, "addition and multiplication only")
        result = left + right if operation == "+" else left*right
        baseline.need(sp.expand(result - target) == 0, "serialized primitive identity")
        primitive_histogram[operation] += 1
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every declared input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "only declared source symbols")
    baseline.need(len(primitives) == sum(histogram.values()) == 112, "112 arithmetic checks")
    baseline.need(primitive_histogram == {"+": 50, "*": 62}, "final histogram")
    constants = quadratic.verify_constants()
    return {"status": "PASS", "operations": 112, "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {"additions": 50, "multiplications": 62},
            "unknowns": 32, "equations": 20, "equality_tests": 20,
            "parameters": PARAMETERS, "positive_input_names": NAMES,
            "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
            "auxiliary_domain": "integers, including the signed expression of-d",
            "primitive_instructions": primitives, "equalities": EQUALITIES,
            "residual_polynomials": records, "support_bounds": support,
            "input_admissibility": {
                "quadratic_rows": "Select an integer residual basis over Q and pad to 1830 rows",
                "coefficient_code": "e_0(B)=z*sum(B^j,j=0..L-1)+D(B); Z=2z",
                "packed_index": "V=e_0(Z)+ell_0(Z)*Z^L",
                "radix_scale": "H a power of two >max(2*Z^(2L+1),Z*1890^2,3L,16)",
                "scope": "Z,V,H are fixed for the represented set, independently of x",
            },
            "proofs": ["../1980/QUADRATIC_MASK_PROOF.md",
                       "../1980/PELL_SHIFTED_BASE_PROOF.md",
                       "../1980/PELL_SIGNED_PROOF.md"],
            "exponent_numeral": str(L), "numerals_from_one": constants,
            "operations_with_numerals_from_one": 112 + constants["operations"],
            "scope": "fixed direct-quadratic indices and the shifted Pell parameter P=1+2UM^2",
            "optimality_claimed": False}


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive unknowns")
    print("Including fixed numeral construction:", receipt["operations_with_numerals_from_one"])
