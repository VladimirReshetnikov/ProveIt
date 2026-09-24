#!/usr/bin/env python3
"""113-operation direct quadratic encoding; preserves the 114-step module.

The mathematical construction is in ../1980/QUADRATIC_MASK_PROOF.md.
The fixed sparse mask serves both the witness support and the list of
quadratic target coefficients. Extra code coordinates at target positions
are harmless by explicitly checked support separation.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round5_1980_certificate as previous
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round6_1980_quadratic_certificate.json"
L = 5 ** 16
ORIGINAL_WITNESSES = 58
ROWS = (ORIGINAL_WITNESSES + 3) * (ORIGINAL_WITNESSES + 2) // 2
MOMENT_MODULUS = 2 * ORIGINAL_WITNESSES ** 2 + 1
VARIABLE_WEIGHTS = tuple(1 + 3 * (MOMENT_MODULUS * i + i * i)
                         for i in range(ORIGINAL_WITNESSES + 1))
VMAX = max(VARIABLE_WEIGHTS)
ROW_SPACING = 4 * VMAX + 1
FIRST_ROW = (ROWS + 1) * ROW_SPACING + 2 * VMAX
LAST_ROW = FIRST_ROW + (ROWS - 1) * ROW_SPACING
CODE_COORDINATES = ORIGINAL_WITNESSES + ROWS
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = dict(previous.SYM)
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def verify_support_bounds():
    baseline.need(ROWS == 1830, "quadratic coefficient-space dimension")
    baseline.need(MOMENT_MODULUS == 6729 and VARIABLE_WEIGHTS[0] == 1,
                  "fixed Sidon construction and input weight")
    monomial_weights = [0] + list(VARIABLE_WEIGHTS) + [
        left + right for i, left in enumerate(VARIABLE_WEIGHTS)
        for right in VARIABLE_WEIGHTS[i:]]
    baseline.need(len(monomial_weights) == len(set(monomial_weights)) == ROWS,
                  "all 1830 quadratic monomials have distinct exact weights")
    baseline.need(ROW_SPACING > 2 * VMAX, "distinct target support intervals")
    baseline.need(FIRST_ROW - 2 * VMAX > VMAX, "automatic zero targets at variable positions")
    baseline.need(2 * FIRST_ROW - 2 * VMAX > LAST_ROW, "dummy coordinates cannot reach target rows")
    baseline.need(L > 3 * LAST_ROW + 1, "fixed exponent exceeds every code and necessity degree")
    baseline.need(3 * LAST_ROW < L and 2 * L - 1 + 2 * LAST_ROW < 3 * L,
                  "coefficient product and offset coverage")
    return {"original_witnesses": ORIGINAL_WITNESSES, "rows": ROWS,
            "code_coordinates": CODE_COORDINATES,
            "variable_weights": list(VARIABLE_WEIGHTS),
            "monomial_weights_distinct": len(monomial_weights),
            "moment_modulus": MOMENT_MODULUS,
            "maximum_variable_weight": str(VMAX),
            "row_spacing": str(ROW_SPACING),
            "first_row_weight": str(FIRST_ROW),
            "last_row_weight": str(LAST_ROW), "exponent": str(L)}


def make_schedule():
    schedule = []
    for target, op, left, right in previous.SCHEDULE:
        if target in {"b4", "C4"}:
            continue
        left = "b2" if target == "B" and left == "b4" else left
        right = "b2" if target == "B" and right == "b4" else right
        left = "C2" if left == "C4" else left
        right = "C2" if right == "C4" else right
        if target == "R20":
            right = L
        schedule.append((target, op, left, right))
    replace_block(schedule, [
        "Tcoef", "Tq3", "bm1", "lbm1", "T2", "b5m2", "b5m2q8", "T",
    ], [
        ("Tcoef", "-", "L2", "zl"),
        ("Tq3", "*", "Tcoef", "q"),
        ("bm1", "-", "b", 1),
        ("lbm1", "*", "l", "bm1"),
        ("T2", "-", "Tq3", "lbm1"),
        ("b5m2", "-", "B", 2),
        ("packed_target_shift", "*", "lq2", "q2"),
        ("mask_term", "*", "b5m2", "packed_target_shift"),
        ("T", "+", "T2", "mask_term"),
    ])
    baseline.need(len(schedule) == 113, "113-operation quadratic schedule")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    b, e, l, g, q, n = (s[v] for v in "b e l g q n".split())
    old_B = s["H"] * b ** 4
    B = s["H"] * b ** 2
    C = 1 + s["x"] * B + g
    source = [res.subs(old_B, B) for res in previous.source_residuals()]
    source[0] = e + l * C ** 2 + s["al"] - q
    S3 = (2 * e - s["Z"] * s["la"]) * C ** 2 + B * s["la"] * (1 + q ** 2)
    S = g + q * (e + l * q + q ** 2 * S3)
    Tp1 = q - (b - 1) * l + s["th"] * s["la"] * q + (B - 2) * l * q ** 3
    source[6] = s["r"] - S * (n ** 2 - n) - Tp1 * (n ** 2 - 1)
    source[-1] = s["ka"] - L - s["Delta"] * (s["a"] - 1)
    return source


def verify_constants():
    schedule = [
        ("two", "+", 1, 1), ("four", "+", "two", "two"),
        ("five", "+", "four", 1),
        ("f2", "*", "five", "five"), ("f4", "*", "f2", "f2"),
        ("f8", "*", "f4", "f4"), ("exponent", "*", "f8", "f8"),
    ]
    env = {}
    histogram = baseline.run_schedule(schedule, env)
    baseline.need([env[name] for name in ["two", "four", "five", "exponent"]]
                  == [2, 4, 5, L], "seven-step literal construction")
    primitives = primitive_instructions(schedule)
    values = {}
    for row in primitives:
        left = row["left"] if isinstance(row["left"], int) else values[row["left"]]
        right = row["right"] if isinstance(row["right"], int) else values[row["right"]]
        values[row["result"]] = left + right if row["operation"] == "+" else left * right
    baseline.need(values["exponent"] == L, "serialized literal construction")
    return {"operations": len(schedule), "histogram": histogram,
            "primitive_instructions": primitives,
            "scope": "Only 2,4,5,L generated from 1; x,Z,V,H remain supplied parameters"}


def verify_certificate():
    support = verify_support_bounds()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1) * (s["f"] ** 2 - 1)
    G_calculated = 1 + (s["a"] + 1) * env["AE"]
    H17 = 2 * s["r"] + 1 + s["j"] * s["c"]
    corrections = {
        6: (s["la"] * source[3] - source[2]) * s["q"] * (s["n"] ** 2 - 1),
        17: source[16] * (s["a"] + 1) * (G_source + G_calculated) * H17 ** 2,
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 21, "twenty-one equations")
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
        def value(name):
            return sp.Integer(name) if isinstance(name, int) else env[name]
        left, right, target = (value(instruction[name]) for name in ["left", "right", "result"])
        operation = instruction["operation"]
        baseline.need(operation in primitive_histogram, "only addition and multiplication")
        expected = left + right if operation == "+" else left * right
        baseline.need(sp.expand(expected - target) == 0, "serialized primitive identity")
        primitive_histogram[operation] += 1
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all original positive inputs used")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "only declared source symbols")
    baseline.need(sum(histogram.values()) == len(primitives) == 113, "113 operations")
    baseline.need(primitive_histogram == {"+": 51, "*": 62}, "quadratic instruction histogram")
    constants = verify_constants()
    return {"status": "PASS", "operations": 113, "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {"additions": 51, "multiplications": 62},
            "unknowns": 33, "equations": 21, "equality_tests": 21,
            "parameters": PARAMETERS, "positive_input_names": NAMES,
            "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
            "primitive_instructions": primitives, "equalities": EQUALITIES,
            "residual_polynomials": records, "support_bounds": support,
            "exponent_numeral": str(L), "numerals_from_one": constants,
            "operations_with_numerals_from_one": 113 + constants["operations"],
            "scope": "fixed admissible direct-quadratic indices, with shared support and target mask",
            "optimality_claimed": False}


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], result["additions_and_multiplications_only"])
    print("including fixed literal construction:", result["operations_with_numerals_from_one"])
