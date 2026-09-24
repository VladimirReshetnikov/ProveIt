#!/usr/bin/env python3
"""Compose the short masks, signed Pell parameter, and linear ratio bounds.

The resulting system has 33 positive witnesses and 21 equations. Its
uniform certificate has 114 addition/multiplication instructions. Exact
polynomial and primitive checks below verify the arithmetic; the separate
normalization, decoding, and positive-domain arguments are indispensable.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_packed_certificate as packed
import round5_1980_short_masks as short
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round5_1980_certificate.json"
L = short.L
PARAMETERS = ["x", "Z", "V", "H"]
NAMES = list(short.NAMES) + ["zeta"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(packed.EQUATION_LABELS)
EQUATION_LABELS[9:10] = ["E10a", "E10b"]
EQUALITIES = list(short.EQUALITIES)
EQUALITIES[9:10] = [("c", "R10a"), ("k", "R10b")]


def make_schedule():
    schedule = list(short.SCHEDULE)
    baseline.need(len(schedule) == 118, "short-mask baseline")
    am1 = [row for row in schedule if row[0] == "am1"]
    baseline.need(am1 == [("am1", "-", "a", 1)], "existing a-1 is unique")
    schedule = [row for row in schedule if row[0] != "am1"]
    replace_block(schedule, ["a2", "A"], [
        am1[0], ("ap1", "+", "a", 1), ("A", "*", "am1", "ap1"),
    ])
    replace_block(schedule, ["dof"], [("dof", "-", "of", "d")])
    replace_block(schedule, ["d2ma", "f2d", "G", "G2", "G2m1"], [
        ("Gminus1", "*", "ap1", "AE"),
        ("Gplus1", "+", "Gminus1", 2),
        ("G2m1", "*", "Gminus1", "Gplus1"),
    ])
    replace_block(schedule, ["ksn2", "cm", "cm2", "f4", "L10"], [
        ("ksn2", "*", "k", "sn2"),
        ("R10a", "+", "ksn2", "eta"),
        ("R10b", "+", "eta", "zeta"),
    ])
    baseline.need(len(schedule) == 114, "combined length")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    source = list(short.source_residuals())
    G = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    source[16] = (s["o"]*s["f"] - s["d"])**2 - (G**2 - 1)*H**2 - 1
    source[9:10] = [s["c"] - s["k"]*s["s"]*s["n"]**2 - s["eta"],
                    s["k"] - s["eta"] - s["zeta"]]
    return source


def verify_constants():
    schedule = [
        ("two", "+", 1, 1), ("four", "+", "two", "two"),
        ("five", "+", "four", 1),
        ("f2", "*", "five", "five"), ("f4", "*", "f2", "f2"),
        ("f8", "*", "f4", "f4"), ("f16", "*", "f8", "f8"),
        ("f32", "*", "f16", "f16"), ("exponent", "*", "f32", "f32"),
    ]
    env = {}
    histogram = baseline.run_schedule(schedule, env)
    baseline.need(env["exponent"] == L == 5**64, "literal L=5^64")
    primitives = primitive_instructions(schedule)
    values = {}
    for row in primitives:
        left = row["left"] if isinstance(row["left"], int) else values[row["left"]]
        right = row["right"] if isinstance(row["right"], int) else values[row["right"]]
        values[row["result"]] = left + right if row["operation"] == "+" else left*right
    baseline.need([values[name] for name in ["two", "four", "five", "exponent"]]
                  == [2, 4, 5, L], "serialized numeral construction")
    return {"operations": len(schedule), "histogram": histogram,
            "primitive_instructions": primitives,
            "scope": "Only 2,4,5,L generated from 1; x,Z,V,H remain supplied parameters"}


def verify_certificate():
    baseline.need(len(NAMES) == len(set(NAMES)) == 37, "37 distinct positive inputs")
    baseline.need(set(PARAMETERS) <= set(NAMES), "all four fixed parameters declared")
    baseline.need(len(set(NAMES) - set(PARAMETERS)) == 33, "33 positive witnesses")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]*(s["n"]**2 - 1),
        17: source[16]*(s["a"] + 1)*(G_source + G_calculated)*H**2,
    }
    baseline.need(len(source) == len(EQUALITIES) == len(EQUATION_LABELS) == 21,
                  "21 explicitly enumerated equations")
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
        records.append({
            "equation": EQUATION_LABELS[index], "equality": [left, right],
            "source_residual_polynomial": sp.sstr(sp.expand(residual)),
            "certificate_residual_polynomial": sp.sstr(actual),
            "source_residual_sign": sign,
            "triangular_correction_polynomial": sp.sstr(sp.expand(correction)),
        })
    primitives = primitive_instructions(SCHEDULE)
    primitive_histogram = {"+": 0, "*": 0}
    for row in primitives:
        operation = row["operation"]
        baseline.need(operation in primitive_histogram, "addition/multiplication only")
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right, target = (value(row[name]) for name in ["left", "right", "result"])
        result = left + right if operation == "+" else left*right
        baseline.need(sp.expand(result - target) == 0, "serialized primitive identity")
        primitive_histogram[operation] += 1
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "only declared source symbols")
    baseline.need(sum(histogram.values()) == len(primitives) == 114, "114 total operations")
    baseline.need(primitive_histogram == {"+": 51, "*": 63}, "final primitive histogram")
    constants = verify_constants()
    return {
        "status": "PASS", "operations": 114, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 51, "multiplications": 63},
        "unknowns": 33, "equations": 21, "equality_tests": len(EQUALITIES),
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "auxiliary_domain": "integers, including signed of-d",
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "exponent_numeral": str(L), "coefficient_witnesses": short.NU,
        "input_admissibility": {
            "normalization": "R=24*S+z*(sigma-1), S the zero-constant gated sum of squares",
            "digits": "R=sum c_i P_i monomials, P_0=-z, -z<P_i<z otherwise; Z=2z",
            "packed_index": "V=e_0(Z)+l_0(Z)*Z^L; L=5^64",
            "radix_scale": "H a power of two >max(2*Z^(2L+1),Z*62^4,3L,64)",
            "scope": "Z,V,H are fixed admissible encoding parameters, not existential witnesses",
        },
        "triangular_identities": [
            "F7calc=F7source+(lambda*F3-F2)*q*(n^2-1)",
            "F17calc=F17source+F16*(a+1)*(G_source+G_calculated)*(2r+1+jc)^2",
        ],
        "proofs": ["../1980/SHORT_MASKS_PROOF.md", "../1980/PELL_SIGNED_PROOF.md",
                   "../1980/PELL_PARITY_PROOF.md", "../1980/PELL_INTERVAL_PROOF.md"],
        "numerals_from_one": constants,
        "operations_with_numerals_from_one": 114 + constants["operations"],
        "scope": "short-mask indices, signed-congruence Pell block, and strict linear ratio bounds",
        "optimality_claimed": False,
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive witnesses")
    print("Every residual and primitive verified exactly;",
          receipt["operations_with_numerals_from_one"], "including fixed literal construction")
    print("wrote", OUT.name)
