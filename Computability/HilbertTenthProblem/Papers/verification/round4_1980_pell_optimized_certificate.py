#!/usr/bin/env python3
"""A 119-operation certificate using Jones's alternate Pell step-down parameter.

This derives from the preserved 120-operation packed certificate.  In E17
use G=a+f^2(f^2-a), explicitly permitted in the remark after Lemma 2.28
of the corrected 1982 source.  The factorization

    G^2-1 = ((f^2-1)(f^2-a+1)) (((f^2-1)(f^2-a+1))+2)

shares f^2-1 from E16 and a-1 from E20, saving one addition.  Its exact
triangular correction is checked against E16; the independent existential
positive-domain proof is ../1980/PELL_ALTERNATE_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_packed_certificate as packed
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_pell_optimized_certificate.json"
NAMES, SYM, PARAMETERS = packed.NAMES, packed.SYM, packed.PARAMETERS
EQUALITIES, EQUATION_LABELS = packed.EQUALITIES, packed.EQUATION_LABELS


def make_schedule():
    schedule = list(packed.SCHEDULE)
    am1_rows = [row for row in schedule if row[0] == "am1"]
    baseline.need(am1_rows == [("am1", "-", "a", 1)], "unique existing a-1")
    schedule = [row for row in schedule if row[0] != "am1"]
    replace_block(schedule, ["d2ma", "f2d", "G", "G2", "G2m1"], [
        am1_rows[0],
        ("F2minusAm1", "-", "L16", "am1"),
        ("Gminus1", "*", "AE", "F2minusAm1"),
        ("Gplus1", "+", "Gminus1", 2),
        ("G2m1", "*", "Gminus1", "Gplus1"),
    ])
    baseline.need(len(schedule) == 119, "119 operations")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(packed.source_residuals())
    s = SYM
    G = s["a"] + s["f"]**2 * (s["f"]**2 - s["a"])
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    source[16] = (s["d"] + s["o"]*s["f"])**2 - ((G**2 - 1)*H**2 + 1)
    return source


def verify_certificate():
    # Inherit verified constant construction and admissibility metadata,
    # while independently checking every residual and primitive below.
    receipt = packed.verify_certificate()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**3*(s["n"]**2 - 1),
    }
    J = s["f"]**2 - s["a"] + 1
    G_source = s["a"] + s["f"]**2*(s["f"]**2 - s["a"])
    G_calculated = 1 + env["AE"]*J
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections[16] = source[15]*J*(G_source + G_calculated)*H**2
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
        baseline.need(op in primitive_histogram, "only addition/multiplication")
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        lv, rv = value(instruction["left"]), value(instruction["right"])
        target = value(instruction["result"])
        baseline.need(sp.expand((lv + rv if op == "+" else lv*rv) - target) == 0,
                      "serialized primitive identity")
        primitive_histogram[op] += 1
    used = {value for _, _, left, right in SCHEDULE for value in (left, right)
            if isinstance(value, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs used")
    baseline.need(len(source) == len(EQUALITIES) == 20, "20 equations")
    baseline.need(sum(histogram.values()) == 119, "119 operations")
    baseline.need(primitive_histogram == {"+": 51, "*": 68}, "primitive histogram")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "source uses only declared inputs")
    receipt.update({
        "operations": 119,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 51, "multiplications": 68},
        "residual_signs": signs,
        "primitive_instructions": primitives,
        "residual_polynomials": records,
        "operations_with_numerals_from_one": 119 + receipt["numerals_from_one"]["operations"],
        "pell_parameter": "G=a+f^2(f^2-a), alternate P5 of Jones 1982 Lemma 2.28",
        "pell_positive_domain_proof": "../1980/PELL_ALTERNATE_PROOF.md",
        "triangular_identities": [
            receipt["triangular_identity"],
            "F17calc=F17alt+F16*(f^2-a+1)*(G_source+G_calculated)*(2r+1+jc)^2",
        ],
        "scope": "admissible packed indices with alternate Pell parameter; f,i,j,o may be re-chosen",
    })
    del receipt["triangular_identity"]
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], "operations", result["straight_line_histogram"],
          ";", result["equality_tests"], "equalities;")
    print("E7 and E17 triangular identities and all primitives verified exactly;")
    print(result["operations_with_numerals_from_one"], "operations including numeral construction.")
    print("wrote", OUT.name)
