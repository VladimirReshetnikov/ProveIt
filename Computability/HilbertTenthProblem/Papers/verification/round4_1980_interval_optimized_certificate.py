#!/usr/bin/env python3
"""117 operations: replace the quadratic approximation by a positive remainder.

E10 becomes c=k*s*n^2+eta and k=eta+zeta, with both remainders positive.
This costs three operations in place of the original five, adding one
positive unknown and one free equality. See ../1980/PELL_INTERVAL_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_parity_optimized_certificate as parity
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_interval_optimized_certificate.json"
NAMES = list(parity.NAMES) + ["zeta"]
SYM = {name: sp.Symbol(name) for name in NAMES}
PARAMETERS = parity.PARAMETERS
EQUALITIES = list(parity.EQUALITIES)
EQUALITIES[9] = ("c", "R10_remainder")
EQUALITIES.insert(10, ("k", "R10_bound"))
EQUATION_LABELS = list(parity.EQUATION_LABELS)
EQUATION_LABELS[9] = "E10a"
EQUATION_LABELS.insert(10, "E10b")


def make_schedule():
    schedule = list(parity.SCHEDULE)
    replace_block(schedule, ["ksn2", "cm", "cm2", "L10"], [
        ("ksn2", "*", "k", "sn2"),
        ("R10_remainder", "+", "ksn2", "eta"),
        ("R10_bound", "+", "eta", "zeta"),
    ])
    baseline.need(len(schedule) == 117, "117 operations")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(parity.source_residuals())
    s = SYM
    source[9] = s["c"] - s["k"]*s["s"]*s["n"]**2 - s["eta"]
    source.insert(10, s["k"] - s["eta"] - s["zeta"])
    return source


def verify_certificate():
    receipt = parity.verify_certificate()
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
        17: source[16]*J*(G_source + G_calculated)*H**2,
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
    baseline.need(len(source) == len(EQUALITIES) == 21, "21 equations")
    baseline.need(sum(histogram.values()) == 117, "117 operations")
    baseline.need(primitive_histogram == {"+": 51, "*": 66}, "primitive histogram")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "source uses only declared inputs")
    receipt.update({
        "operations": 117,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 51, "multiplications": 66},
        "residual_signs": signs,
        "primitive_instructions": primitives,
        "equalities": EQUALITIES,
        "equality_tests": 21,
        "equations": 21,
        "unknowns": 33,
        "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "residual_polynomials": records,
        "operations_with_numerals_from_one": 117 + receipt["numerals_from_one"]["operations"],
        "interval_positive_domain_proof": "../1980/PELL_INTERVAL_PROOF.md",
        "E10": ["c=k*s*n^2+eta", "k=eta+zeta"],
        "scope": "admissible packed indices with alternate Pell parameter and positive remainder interval; eta,zeta,j,o may be re-chosen",
        "remainder_witnesses": {
            "eta": "c-k*s*n^2",
            "zeta": "k-eta",
            "positivity": "proved from parity rounding and the first nonzero binomial tail term",
        },
    })
    del receipt["eta_maps"]
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS:", result["operations"], "operations", result["straight_line_histogram"],
          ";", result["equality_tests"], "equalities;")
    print("All primitive and residual identities verified exactly;")
    print(result["operations_with_numerals_from_one"], "operations including numeral construction.")
    print("wrote", OUT.name)
