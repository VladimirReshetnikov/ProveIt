#!/usr/bin/env python3
"""109-operation certificate with the input in the unit coordinate.

The mathematical encoding proof is separate from these symbolic identities.
Every earlier certificate is preserved unchanged.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round8_1980_certificate as previous
import round6_1980_quadratic_certificate as quadratic
from round4_1980_optimized_certificate import primitive_instructions

HERE = Path(__file__).resolve().parent
OUT = HERE / "round9_1980_certificate.json"
L = previous.L
ORIGINAL_WITNESSES = 58
EXTRA_GUARD_WITNESSES = 1
LAST_VARIABLE = ORIGINAL_WITNESSES + EXTRA_GUARD_WITNESSES
BASE_ROWS = 1830
ROWS = BASE_ROWS + 2
MOMENT_MODULUS = 2*LAST_VARIABLE**2 + 1
VARIABLE_WEIGHTS = tuple(1 + 3*(MOMENT_MODULUS*i + i*i)
                         for i in range(LAST_VARIABLE + 1))
VMAX = max(VARIABLE_WEIGHTS)
ROW_SPACING = 4*VMAX + 1
FIRST_ROW = (ROWS + 1)*ROW_SPACING + 2*VMAX
LAST_ROW = FIRST_ROW + (ROWS - 1)*ROW_SPACING
K = LAST_ROW + 1
CODE_COORDINATES = LAST_VARIABLE + ROWS + 1  # all positive-weight coordinates; input is unit
COEFFICIENT_BOUND = 1900
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "xb5":
            baseline.need((operation, left, right) == ("*", "x", "B"),
                          "the unique input-position multiplication")
            continue
        if left == "xb5":
            left = "x"
        if right == "xb5":
            right = "x"
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 109, "one input-position multiplication removed")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    b, e, ell, g, q, n = (s[name] for name in "b e l g q n".split())
    B = s["H"]*b**2
    C = s["x"] + g
    Y = ell + e*q
    S3 = (2*e - s["Z"]*s["la"])*C**2 + B*s["la"]*(1 + q)
    S = g + q**2*(Y + q**2*S3)
    Tplus = q**2 - (b - 1)*ell + s["th"]*s["la"]*q**2 + (B - 4)*ell*q**4
    source[0] = Y + C**2 + s["al"] - q**2
    source[4] = Y - s["V"] - s["t"]*s["th"]
    source[6] = s["r"] - S*(n**2 - n) - Tplus*(n**2 - 1)
    source[-1] = S3 - s["sigma"]
    return source


def verify_support_bounds():
    baseline.need(LAST_VARIABLE == 59 and ROWS == 1832, "one guard coordinate and two rows")
    weights = [0] + list(VARIABLE_WEIGHTS) + [
        left + right for i, left in enumerate(VARIABLE_WEIGHTS)
        for right in VARIABLE_WEIGHTS[i:]]
    baseline.need(len(weights) == len(set(weights)) == 1891,
                  "all homogeneous quadratic weights including the unit are distinct")
    baseline.need(MOMENT_MODULUS == 6963 and VARIABLE_WEIGHTS[0] == 1,
                  "decoded unit-coordinate weight and exact Sidon modulus")
    baseline.need(VMAX == 1242895 and LAST_ROW == 18218358574, "exact layout values")
    baseline.need(ROW_SPACING > 2*VMAX, "row supports are disjoint")
    baseline.need(FIRST_ROW - 2*VMAX > VMAX, "low tests including the unit are automatic")
    baseline.need(2*FIRST_ROW - 2*VMAX > LAST_ROW, "dummy coordinate separation")
    baseline.need(L > 3*K + 2, "integer product ends strictly below the high mask")
    baseline.need(CODE_COORDINATES + 1 == 1893 < COEFFICIENT_BOUND,
                  "uniform sum of coordinate bounds")
    return {"original_witnesses": ORIGINAL_WITNESSES, "guard_witnesses": 1,
            "base_rows": BASE_ROWS, "rows": ROWS, "positive_weight_coordinates": 60,
            "code_coordinates_excluding_input": CODE_COORDINATES,
            "coordinates_including_input": CODE_COORDINATES + 1,
            "coefficient_bound": COEFFICIENT_BOUND, "input_weight": 0,
            "decoded_unit_weight": 1,
            "variable_weights": list(VARIABLE_WEIGHTS),
            "monomial_weights_distinct": len(weights), "moment_modulus": MOMENT_MODULUS,
            "maximum_variable_weight": str(VMAX), "row_spacing": str(ROW_SPACING),
            "first_row_weight": str(FIRST_ROW), "last_row_weight": str(LAST_ROW),
            "short_baseline_length": str(K), "exponent": str(L)}


def verify_certificate():
    support = verify_support_bounds()
    baseline.need(len(NAMES) == len(set(NAMES)) == 37, "37 distinct positive inputs")
    baseline.need(len(set(NAMES) - set(PARAMETERS)) == 33, "33 positive unknowns")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**2*(s["n"]**2 - 1),
        16: source[15]*(s["a"] + 1)*(G_source + G_calculated)*H17**2,
    }
    baseline.need(len(source) == len(EQUALITIES) == len(EQUATION_LABELS) == 21,
                  "21 explicit source equations and tests")
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
    baseline.need(len(primitives) == sum(histogram.values()) == 109, "109 arithmetic checks")
    baseline.need(primitive_histogram == {"+": 49, "*": 60}, "final histogram")
    constants = quadratic.verify_constants()
    return {"status": "PASS", "operations": 109, "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {"additions": 49, "multiplications": 60},
            "unknowns": 33, "equations": 21, "equality_tests": 21,
            "parameters": PARAMETERS, "positive_input_names": NAMES,
            "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
            "auxiliary_domain": "integers, including the signed expression of-d",
            "positive_register": {"register": "S3", "positive_unknown": "sigma",
                                  "enforcement": "the free equality S3=sigma"},
            "primitive_instructions": primitives, "equalities": EQUALITIES,
            "residual_polynomials": records, "support_bounds": support,
            "input_admissibility": {
                "quadratic_rows": "Homogenize 1830 original basis rows; add u*delta-x^2 and special delta^2 test",
                "special_target": "Ordinary targets 2*F are even; delta has weight1 and special delta^2 term uses weight2",
                "support_code": "ell_0(B)=sum(60 positive coordinate powers)+sum(1832 row powers); unit input excluded",
                "coefficient_code": "e_0(B)=z*sum(B^j,j=0..K-1)+D(B); Z=2z; K=t_last+1",
                "packed_index": "V=ell_0(Z)+e_0(Z)*Z^L",
                "radix_scale": "H a power of two >max(2*Z^(2L+1),4^(t_last+3)*Z*1900^2,3L,16)",
                "scope": "Z,V,H are fixed for the represented set, independently of x",
            },
            "proofs": ["../1980/INPUT_UNIT_PROOF.md", "../1980/PELL_RELAXED_RADIX_PROOF.md",
                       "../1980/UNIT_DIGIT_PROOF.md", "../1980/REVERSED_PACKING_PROOF.md",
                       "../1980/QUADRATIC_MASK_PROOF.md",
                       "../1980/PELL_SHIFTED_BASE_PROOF.md",
                       "../1980/PELL_SIGNED_PROOF.md"],
            "exponent_numeral": str(L), "numerals_from_one": constants,
            "operations_with_numerals_from_one": 109 + constants["operations"],
            "scope": "arithmetic identities for the unit-position input and reversed homogeneous quadratic packing",
            "optimality_claimed": False}


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive unknowns")
    print("Including fixed numeral construction:", receipt["operations_with_numerals_from_one"])
