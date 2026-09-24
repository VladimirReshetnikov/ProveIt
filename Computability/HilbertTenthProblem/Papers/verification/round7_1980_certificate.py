#!/usr/bin/env python3
"""111-operation reversed packing certificate, with exact arithmetic verification.

The mathematical encoding proof is separate from these symbolic identities.
Every earlier certificate is preserved unchanged.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round6_1980_certificate as previous
import round6_1980_quadratic_certificate as quadratic
from round4_1980_optimized_certificate import primitive_instructions

HERE = Path(__file__).resolve().parent
OUT = HERE / "round7_1980_certificate.json"
L = previous.L
K = quadratic.LAST_ROW + 1
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES) + ["sigma"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUALITIES[0] = ("L1", "q2")
EQUALITIES.append(("S3", "sigma"))
EQUATION_LABELS = list(previous.EQUATION_LABELS) + ["S3_positive"]


def make_schedule():
    replacements = {
        "lq2": ("eq", "*", "e", "q"),
        "S2": ("S2", "+", "l", "eq"),
        "bound_sum": ("bound_sum", "+", "S2", "C2"),
        "q4p1": ("qp1", "+", "q", 1),
        "P2": ("P2", "*", "Lam", "qp1"),
        "Sq3": ("Sq4", "*", "Sin", "q2"),
        "S": ("S", "+", "g", "Sq4"),
        "Tq3": ("Tq4", "*", "Tcoef", "q2"),
        "T2": ("T2", "-", "Tq4", "lbm1"),
        "packed_target_shift": ("packed_target_shift", "*", "l", "q4"),
    }
    schedule = [replacements.get(row[0], row) for row in previous.SCHEDULE
                if row[0] != "lC4"]
    baseline.need(len(schedule) == 111, "one bound multiplication removed")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    b, e, ell, g, q, n = (s[name] for name in "b e l g q n".split())
    B = s["H"]*b**2
    C = 1 + s["x"]*B + g
    Y = ell + e*q
    S3 = (2*e - s["Z"]*s["la"])*C**2 + B*s["la"]*(1 + q)
    S = g + q**2*(Y + q**2*S3)
    Tplus = q**2 - (b - 1)*ell + s["th"]*s["la"]*q**2 + (B - 2)*ell*q**4
    source[0] = Y + C**2 + s["al"] - q**2
    source[4] = Y - s["V"] - s["t"]*s["th"]
    source[6] = s["r"] - S*(n**2 - n) - Tplus*(n**2 - 1)
    source.append(S3 - s["sigma"])
    return source


def verify_certificate():
    support = quadratic.verify_support_bounds()
    baseline.need(3*quadratic.LAST_ROW < L, "short coefficient products lie below L")
    baseline.need(K == quadratic.LAST_ROW + 1 < L, "short baseline length")
    baseline.need(L > 3*K + 2, "integer coefficient product ends below the high mask")
    support["short_baseline_length"] = str(K)
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
    baseline.need(len(primitives) == sum(histogram.values()) == 111, "111 arithmetic checks")
    baseline.need(primitive_histogram == {"+": 50, "*": 61}, "final histogram")
    constants = quadratic.verify_constants()
    return {"status": "PASS", "operations": 111, "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {"additions": 50, "multiplications": 61},
            "unknowns": 33, "equations": 21, "equality_tests": 21,
            "parameters": PARAMETERS, "positive_input_names": NAMES,
            "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
            "auxiliary_domain": "integers, including the signed expression of-d",
            "positive_register": {"register": "S3", "positive_unknown": "sigma",
                                  "enforcement": "the free equality S3=sigma"},
            "primitive_instructions": primitives, "equalities": EQUALITIES,
            "residual_polynomials": records, "support_bounds": support,
            "input_admissibility": {
                "quadratic_rows": "Select an integer residual basis over Q and pad to 1830 rows",
                "coefficient_code": "e_0(B)=z*sum(B^j,j=0..K-1)+D(B); Z=2z; K=t_last+1",
                "packed_index": "V=ell_0(Z)+e_0(Z)*Z^L",
                "radix_scale": "H a power of two >max(2*Z^(2L+1),2^(t_last+4)*Z*1890^2,3L,16)",
                "scope": "Z,V,H are fixed for the represented set, independently of x",
            },
            "proofs": ["../1980/REVERSED_PACKING_PROOF.md",
                       "../1980/QUADRATIC_MASK_PROOF.md",
                       "../1980/PELL_SHIFTED_BASE_PROOF.md",
                       "../1980/PELL_SIGNED_PROOF.md"],
            "exponent_numeral": str(L), "numerals_from_one": constants,
            "operations_with_numerals_from_one": 111 + constants["operations"],
            "scope": "arithmetic identities for reversed direct-quadratic packing and shifted Pell P",
            "optimality_claimed": False}


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive unknowns")
    print("Including fixed numeral construction:", receipt["operations_with_numerals_from_one"])
