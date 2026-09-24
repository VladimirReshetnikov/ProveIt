#!/usr/bin/env python3
"""118 operations: remove the factor 4 in E10 using a parity rounding proof.

Derived from the preserved 119-operation alternate-Pell certificate.
The new E10 is (c-k*s*n^2)^2+eta=k^2. Its weaker approximation suffices
because the other equations force n even before the final rounding step.
See ../1980/PELL_PARITY_PROOF.md for the noncircular positive-domain proof.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_pell_optimized_certificate as pell
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_parity_optimized_certificate.json"
NAMES, SYM, PARAMETERS = pell.NAMES, pell.SYM, pell.PARAMETERS
EQUALITIES, EQUATION_LABELS = pell.EQUALITIES, pell.EQUATION_LABELS


def make_schedule():
    schedule = list(pell.SCHEDULE)
    replace_block(schedule, ["f4", "L10"], [("L10", "+", "cm2", "eta")])
    baseline.need(len(schedule) == 118, "118 operations")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(pell.source_residuals())
    s = SYM
    source[9] = (s["c"] - s["k"]*s["s"]*s["n"]**2)**2 + s["eta"] - s["k"]**2
    return source


def verify_certificate():
    receipt = pell.verify_certificate()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    J = s["f"]**2 - s["a"] + 1
    G_source = s["a"] + s["f"]**2*(s["f"]**2 - s["a"])
    G_calculated = 1 + env["AE"]*J
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**3*(s["n"]**2 - 1),
        16: source[15]*J*(G_source + G_calculated)*H**2,
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
    baseline.need(sum(histogram.values()) == 118, "118 operations")
    baseline.need(primitive_histogram == {"+": 51, "*": 67}, "primitive histogram")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "source uses only declared inputs")
    receipt.update({
        "operations": 118,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 51, "multiplications": 67},
        "residual_signs": signs,
        "primitive_instructions": primitives,
        "residual_polynomials": records,
        "operations_with_numerals_from_one": 118 + receipt["numerals_from_one"]["operations"],
        "rounding_positive_domain_proof": "../1980/PELL_PARITY_PROOF.md",
        "E10": "(c-k*s*n^2)^2+eta=k^2",
        "eta_maps": {
            "weak_from_strong": "eta_weak=eta_strong+3*(c-k*s*n^2)^2",
            "strong_from_weak": "eta_strong=4*eta_weak-3*k^2; positivity proved using parity",
        },
        "scope": "admissible packed indices with alternate Pell parameter and parity rounding; eta,j,o may be re-chosen",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], "operations", result["straight_line_histogram"],
          ";", result["equality_tests"], "equalities;")
    print("All primitive and residual identities verified exactly;")
    print(result["operations_with_numerals_from_one"], "operations including numeral construction.")
    print("wrote", OUT.name)
