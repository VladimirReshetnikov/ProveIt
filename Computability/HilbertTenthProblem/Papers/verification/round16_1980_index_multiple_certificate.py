#!/usr/bin/env python3
"""105 operations: arrange M=(r+1)*Y and require k=h*(r+1).

P=2*U*M^2+1 is congruent to1 modulo r+1. The Pell index is therefore
a positive multiple of r+1; growth and the positive ratio interval exclude
all multiples after the first. PELL_INDEX_MULTIPLE_PROOF.md proves this
replacement and its positive witness construction. No predecessor is edited.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round14_1980_base_four_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round16_1980_index_multiple_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
baseline.need(EQUATION_LABELS[10] == "E11" and EQUALITIES[10] == ("k", "R11"),
              "the changed index equality is identified explicitly")
EQUALITIES[10] = ("k", "hpm1")


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "r1":
            baseline.need((operation, left, right) == ("+", "r", 1),
                          "move the existing r+1 register without copying it")
            continue
        if target == "rsn2":
            baseline.need((operation, left, right) == ("*", "r", "sn2"),
                          "replace M=rY by M=(r+1)Y")
            schedule.append(("r1", "+", "r", 1))
            left = "r1"
        if target == "hpm1":
            baseline.need((operation, left, right) == ("*", "h", "wsq"),
                          "replace the old index quotient product")
            right = "r1"
        if target == "R11":
            baseline.need((operation, left, right) == ("+", "r1", "hpm1"),
                          "the sole removed addition")
            continue
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 105, "one index addition is removed")
    return schedule


SCHEDULE = make_schedule()
NUMERAL_SCHEDULE = list(previous.NUMERAL_SCHEDULE)
LITERAL_REGISTERS = dict(previous.LITERAL_REGISTERS)
STRICT_SCHEDULE = NUMERAL_SCHEDULE + [
    (target, operation, LITERAL_REGISTERS.get(left, left),
     LITERAL_REGISTERS.get(right, right))
    for target, operation, left, right in SCHEDULE
]


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    U = s["w"]*s["n"]**2
    M = (s["r"] + 1)*s["s"]*s["n"]**2
    Q = U*M**2
    baseline.need(EQUATION_LABELS[7] == "E9" and EQUATION_LABELS[11] == "E12",
                  "explicit positions of the changed norm and parameter definition")
    source[7] = Q*(Q + 1)*s["k"]**2 - s["tau"]*(s["tau"] + 1)
    source[10] = s["k"] - s["h"]*(s["r"] + 1)
    source[11] = s["a"] - M*(U + 1)
    return source


def verify_certificate():
    receipt = previous.verify_certificate()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A = s["a"] + 4
    G_source = 1 + (A + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (A + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**2*(s["n"]**2 - 1),
        16: source[15]*(A + 1)*(G_source + G_calculated)*H17**2,
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 source equations and tests")
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
    U = s["w"]*s["n"]**2
    M = (s["r"] + 1)*s["s"]*s["n"]**2
    for name, expected in {
        "r1": s["r"] + 1, "rsn2": M, "wsq": U*M**2,
        "R12": M*(U + 1), "hpm1": s["h"]*(s["r"] + 1),
        "tr1": 2*s["r"] + 1,
    }.items():
        baseline.need(sp.expand(env[name] - expected) == 0, "exact changed register " + name)
    baseline.need("R11" not in env, "the old index-sum register no longer exists")
    for index, residual in enumerate(previous.source_residuals()):
        if index not in {7, 10, 11}:
            baseline.need(sp.expand(source[index] - residual) == 0,
                          "all other source polynomials are unchanged")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 105 and primitive_histogram == {"+": 46, "*": 59},
                  "105-operation core histogram")
    strict_env = dict(SYM)
    strict_histogram = baseline.run_schedule(STRICT_SCHEDULE, strict_env)
    strict_primitives, strict_primitive_histogram = verify_primitives(STRICT_SCHEDULE, strict_env)
    baseline.need(len(strict_primitives) == 114 and
                  strict_primitive_histogram == {"+": 50, "*": 64}, "full114 strict certificate")
    baseline.need({operand for _, _, left, right in STRICT_SCHEDULE
                   for operand in (left, right) if isinstance(operand, int)} == {1},
                  "the strict schedule uses only literal one")
    for name in env:
        baseline.need(sp.expand(strict_env[name] - env[name]) == 0,
                      "strict and core registers agree exactly")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    receipt.update({
        "operations": 105, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 46, "multiplications": 59},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "reparameterized_inputs": receipt["reparameterized_inputs"] | {
            "a": "positive a0=(R+1)*Y*(U+1), mathematical main Pell parameter A=a0+4",
            "h": "positive quotient K/(R+1); new E11 is K=h*(R+1)",
            "M": "(R+1)*Y; calculated register rsn2, not an additional input",
            "Q": "U*M^2=w*(r+1)^2*s^2*n^6, already register wsq; not an extra input",
        },
        "exact_witness_identities": [
            "tau_old=2*tau+1 gives the ordinary Pell norm with P=2*Q+1",
            "P-1=2*U*(R+1)^2*Y^2 is divisible by R+1",
            "h=psi_P(R+1)/(R+1) is a positive integer by the Pell congruence",
        ],
        "operations_with_numerals_from_one": 114,
        "strict_certificate": {"operations": 114, "straight_line_histogram": strict_histogram,
            "additions_and_multiplications_only": {"additions": 50, "multiplications": 64},
            "primitive_instructions": strict_primitives, "equalities": EQUALITIES,
            "only_literal": 1},
        "proofs": receipt["proofs"] + ["../1980/PELL_INDEX_MULTIPLE_PROOF.md"],
        "scope": "105 core operations by arranging M=(R+1)*Y and forcing the first Pell index to be a positive multiple of R+1;114 with the inherited numeral chain",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"],
          ";", result["operations_with_numerals_from_one"], "with numerals from one;")
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
