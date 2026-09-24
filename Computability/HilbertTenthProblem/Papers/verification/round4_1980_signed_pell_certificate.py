#!/usr/bin/env python3
"""118-operation candidate using the signed-congruence Pell step-down lemma.

Use G=1+(a+1)(f^2-1) and (of-d)^2 in E17.  The positive-domain proof,
including the necessary signed extension of the chi step-down lemma, is in
../1980/PELL_SIGNED_PROOF.md. This extends the preserved 119-operation
certificate and verifies every residual and serialized primitive exactly.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_pell_optimized_certificate as previous
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_signed_pell_certificate.json"
NAMES, SYM, PARAMETERS = previous.NAMES, previous.SYM, previous.PARAMETERS
EQUALITIES, EQUATION_LABELS = previous.EQUALITIES, previous.EQUATION_LABELS


def make_schedule():
    schedule = [row for row in previous.SCHEDULE if row[0] != "am1"]
    replace_block(schedule, ["a2", "A"], [
        ("am1", "-", "a", 1),
        ("ap1", "+", "a", 1),
        ("A", "*", "am1", "ap1"),
    ])
    replace_block(schedule, ["dof"], [("dof", "-", "of", "d")])
    replace_block(schedule, ["F2minusAm1", "Gminus1", "Gplus1", "G2m1"], [
        ("Gminus1", "*", "ap1", "AE"),
        ("Gplus1", "+", "Gminus1", 2),
        ("G2m1", "*", "Gminus1", "Gplus1"),
    ])
    baseline.need(len(schedule) == 118, "118-operation signed Pell schedule")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    G = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    source[16] = (s["o"]*s["f"] - s["d"])**2 - ((G**2 - 1)*H**2 + 1)
    return source


def verify_certificate():
    receipt = previous.verify_certificate()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**3*(s["n"]**2 - 1),
        16: source[15]*(s["a"] + 1)*(G_source + G_calculated)*H**2,
    }
    signs, records = [], []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual - residual - correction) == 0:
            signs.append(1)
        elif correction == 0 and sp.expand(actual + residual) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"residual mismatch at {EQUATION_LABELS[index]}")
        records.append({
            "equation": EQUATION_LABELS[index], "equality": [left, right],
            "source_residual_polynomial": sp.sstr(sp.expand(residual)),
            "certificate_residual_polynomial": sp.sstr(actual),
            "source_residual_sign": signs[-1],
            "triangular_correction_polynomial": sp.sstr(sp.expand(correction)),
        })
    primitives = primitive_instructions(SCHEDULE)
    primitive_histogram = {"+": 0, "*": 0}
    for instruction in primitives:
        op = instruction["operation"]
        baseline.need(op in primitive_histogram, "only addition and multiplication")
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right, target = (value(instruction[name]) for name in ["left", "right", "result"])
        baseline.need(sp.expand((left + right if op == "+" else left*right) - target) == 0,
                      "serialized primitive identity")
        primitive_histogram[op] += 1
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every declared positive input used")
    baseline.need(len(source) == len(EQUALITIES) == 20, "twenty source residuals")
    baseline.need(sum(histogram.values()) == 118, "118 operations")
    baseline.need(primitive_histogram == {"+": 50, "*": 68}, "118 primitive histogram")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "only declared source inputs")
    receipt.update({
        "operations": 118,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 50, "multiplications": 68},
        "residual_signs": signs,
        "primitive_instructions": primitives,
        "residual_polynomials": records,
        "operations_with_numerals_from_one": 118 + receipt["numerals_from_one"]["operations"],
        "pell_parameter": "G=1+(a+1)(f^2-1); E17 left side is (of-d)^2",
        "pell_positive_domain_proof": "../1980/PELL_SIGNED_PROOF.md",
        "triangular_identities": [
            "F7calc=F7source+(lambda*F3-F2)*q^3*(n^2-1)",
            "F17calc=F17source+F16*(a+1)*(G_source+G_calculated)*(2r+1+jc)^2",
        ],
        "scope": "admissible packed indices with signed-congruence Pell parameter; f,i,j,o may be re-chosen",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], "operations", result["straight_line_histogram"],
          ";", result["equality_tests"], "equalities;")
    print("E7/E17 triangular corrections and every primitive verified exactly;")
    print(result["operations_with_numerals_from_one"], "operations including numeral construction.")
    print("wrote", OUT.name)
