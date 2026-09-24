#!/usr/bin/env python3
"""A 120-operation certificate using one packed coefficient congruence.

The admissible index is (Z,V,H). At the metalevel, let (Z/2,u,y) be a
Jones index, L=5**59, V=y+u*Z**(2*L), and let H be a power of two greater
than max(2*Z**(4*L+1),Z*60**4,3*L). Input x is the remaining parameter.

The radix is B=H*b**4. The bound e*l*C**2<q**2, with C=1+x*B+g, shares
the square C**2 already needed for C**4. The two congruences for e and l
become one for e+l*q**2, with its target digits encoded in V. The original
129-operation schedule is retained in its original module. This script
derives its own deterministic schedule, applies all three independent
algebraic/Pell improvements, and verifies every residual exactly, recording
the E7 identity modulo the already verified E2 and E3.

See ../1980/PACKED_RECODING_PROOF.md for the positive-domain equivalence;
symbolic expansion alone does not establish that mathematical theorem.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_recoded_certificate as recoded
from round4_1980_optimized_certificate import (
    primitive_instructions,
    replace_block,
    verify_recoded_constants,
)

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_packed_certificate.json"
L = recoded.L


def make_schedule():
    schedule = []
    for target, op, left, right in recoded.SCHEDULE:
        if target in {"g2", "elg2", "L1", "tth", "R4", "mth", "R5"}:
            continue
        schedule.append((target, op, left, right))
        if target == "S2":
            schedule.extend([("pack_tth", "*", "t", "th"),
                             ("pack_rhs", "+", "V", "pack_tth")])
        if target == "C2":
            schedule.extend([("elC2", "*", "el", "C2"),
                             ("L1", "+", "elC2", "al")])
    baseline.need(len(schedule) == 123, "packed recoding before other savings")
    replace_block(schedule, [
        "bl", "q3bl", "T1", "thl", "thlq3", "T2", "b5m2", "b5m2q8", "T",
    ], [
        ("Tcoef", "-", "L2", "zl"),
        ("Tq3", "*", "Tcoef", "q3"),
        ("bm1", "-", "b", 1),
        ("lbm1", "*", "l", "bm1"),
        ("T2", "-", "Tq3", "lbm1"),
        ("b5m2", "-", "B", 2),
        ("b5m2q8", "*", "b5m2", "q8"),
        ("T", "+", "T2", "b5m2q8"),
    ])
    replace_block(schedule, [
        "wn2", "wn2p1", "sn2", "rsn2", "R12", "rsn2sq", "wsq", "R8",
    ], [
        ("wn2", "*", "w", "n2"),
        ("sn2", "*", "s", "n2"),
        ("rsn2", "*", "r", "sn2"),
        ("UM", "*", "wn2", "rsn2"),
        ("R12", "+", "UM", "rsn2"),
        ("wsq", "*", "UM", "rsn2"),
        ("R8", "*", 2, "wsq"),
    ])
    replace_block(schedule, ["tk", "R13"], [("R13", "+", "ka", "phi")])
    baseline.need(len(schedule) == 120, "120-operation final schedule")
    return schedule


SCHEDULE = make_schedule()
EQUALITIES = list(recoded.EQUALITIES)
EQUALITIES[4] = ("S2", "pack_rhs")
del EQUALITIES[5]
NAMES = [name for name in recoded.NAMES if name not in {"u", "y", "m"}] + ["V"]
SYM = {name: sp.Symbol(name) for name in NAMES}
PARAMETERS = ["x", "Z", "V", "H"]
EQUATION_LABELS = [
    "E1a", "E1b", "E2", "E3", "E4/E5 packed", "E6", "E7", "E8",
    "E9", "E10", "E11", "E12", "E13", "E14", "E15", "E16", "E17",
    "E18", "E19", "E20",
]


def source_residuals():
    s = SYM
    B = s["H"] * s["b"] ** 4
    C = 1 + s["x"] * B + s["g"]
    source = list(recoded.source_residuals())
    source[0] = s["e"] * s["l"] * C ** 2 + s["al"] - s["q"] ** 2
    source[4] = s["e"] + s["l"] * s["q"] ** 2 - s["V"] - s["t"] * s["th"]
    del source[5]
    source[12] = s["c"] - s["ka"] - s["phi"]
    return source


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    correction = (s["la"] * source[3] - source[2]) * s["q"] ** 3 * (s["n"] ** 2 - 1)
    signs = []
    residual_records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        if index == 6:
            baseline.need(sp.expand(actual - residual - correction) == 0,
                          "E7 triangular residual identity")
            signs.append(1)
        elif sp.expand(actual - residual) == 0:
            signs.append(1)
        elif sp.expand(actual + residual) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"residual mismatch at index {index}: {left}={right}")
        residual_records.append({
            "equation": EQUATION_LABELS[index],
            "equality": [left, right],
            "source_residual_polynomial": sp.sstr(sp.expand(residual)),
            "certificate_residual_polynomial": sp.sstr(actual),
            "source_residual_sign": signs[-1],
            "triangular_correction_polynomial": sp.sstr(sp.expand(correction)) if index == 6 else "0",
        })
    used = {value for _, _, left, right in SCHEDULE for value in (left, right)
            if isinstance(value, str)}
    used |= {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all parameters and unknowns are used")
    baseline.need(len(EQUALITIES) == len(source) == 20, "twenty equalities")
    baseline.need(sum(histogram.values()) == 120, "120 operations")
    baseline.need(set().union(*(residual.free_symbols for residual in source)) <= set(SYM.values()),
                  "all residual symbols are declared inputs")

    # Every subtraction target = left - right becomes the primitive statement
    # target + right = left. Check these serialized statements independently
    # against the symbolic environment used to verify the schedule.
    primitives = primitive_instructions(SCHEDULE)
    primitive_histogram = {"+": 0, "*": 0}
    for instruction in primitives:
        op = instruction["operation"]
        baseline.need(op in primitive_histogram, "only addition and multiplication primitives")
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right = value(instruction["left"]), value(instruction["right"])
        target = value(instruction["result"])
        computed = left + right if op == "+" else left * right
        baseline.need(sp.expand(computed - target) == 0,
                      "serialized primitive instruction agrees exactly with its assignment")
        primitive_histogram[op] += 1
    baseline.need(primitive_histogram == {"+": 52, "*": 68}, "primitive histogram")

    constants = verify_recoded_constants()
    # Re-evaluate the emitted constant statements themselves, so that the JSON
    # receipt certifies the explicit 11-step construction as well as its count.
    constant_values = {}
    for instruction in constants["primitive_instructions"]:
        def constant_value(operand):
            return operand if isinstance(operand, int) else constant_values[operand]
        left = constant_value(instruction["left"])
        right = constant_value(instruction["right"])
        constant_values[instruction["result"]] = (
            left + right if instruction["operation"] == "+" else left * right
        )
    baseline.need(
        [constant_values[name] for name in ["two", "four", "five", "f59"]] == [2, 4, 5, L],
        "serialized constant chain constructs 2,4,5,5^59 from 1",
    )
    return {"status": "PASS", "operations": 120,
            "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {
                "additions": histogram["+"] + histogram["-"],
                "multiplications": histogram["*"]},
            "equality_tests": 20, "residual_signs": signs,
            "unknowns": 32, "parameters": PARAMETERS,
            "positive_input_names": NAMES,
            "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
            "auxiliary_domain": "integers, including negative integers",
            "input_admissibility": {
                "exponent": "L = 5^59",
                "original_index": "(z,u,y) is an admissible Jones index; Z = 2z",
                "packed_index": "V = y + u Z^(2L)",
                "radix_scale": "H is a power of two greater than max(2 Z^(4L+1), Z 60^4, 3L)",
                "certificate_input": "x,Z,V,H are supplied input parameters; H and V construction is outside certificate verification",
            },
            "equations": 20, "exponent_numeral": str(L),
            "triangular_identity": "F7new=F7old+(lambda*F3-F2)*q^3*(n^2-1)",
            "primitive_instructions": primitives,
            "equalities": EQUALITIES,
            "residual_polynomials": residual_records,
            "numerals_from_one": constants,
            "operations_with_numerals_from_one": 120 + constants["operations"],
            "numeral_construction_scope": "Only 2,4,5,L are generated from 1; H,V,Z,x remain supplied encoding and input parameters",
            "scope": "admissible packed indices; positive-domain proof is separate",
            "optimality_claimed": False}


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], "operations", result["straight_line_histogram"],
          ";", result["equality_tests"], "equalities;")
    print("Every primitive and residual verified symbolically;",
          result["operations_with_numerals_from_one"], "operations including numeral construction.")
    print("wrote", OUT.name)
