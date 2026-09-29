#!/usr/bin/env python3
"""106 core / 112 strict operations using a first-Pell index multiple.

In the base-two modular-Sidon system put M=(r+1)*s*n^2 and Q=w*n^2*M^2,
then replace k=r+1+h*Q by k=h*(r+1). The common index-multiple growth
proof forces the same exact Pell index r+1. The base-two ratio and all
positive-domain witnesses are checked in BASE_TWO_INDEX_MULTIPLE_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round13_1980_certificate as previous

HERE = Path(__file__).resolve().parent
OUT = HERE / "round17_1980_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
baseline.need(EQUALITIES[10] == ("k", "R11"), "the old index equality")
EQUALITIES[10] = ("k", "hpm1")


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "r1":
            baseline.need((operation, left, right) == ("+", "r", 1),
                          "the existing index successor is moved, not copied")
            continue
        if target == "rsn2":
            baseline.need((operation, left, right) == ("*", "r", "sn2"),
                          "the old M=RY calculation")
            schedule.append(("r1", "+", "r", 1))
            left = "r1"
        if target == "hpm1":
            baseline.need((operation, left, right) == ("*", "h", "wsq"),
                          "the old congruence product")
            right = "r1"
        if target == "R11":
            baseline.need((operation, left, right) == ("+", "r1", "hpm1"),
                          "the eliminated index-congruence addition")
            continue
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 106, "one addition is eliminated")
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
    U, Y = s["w"]*s["n"]**2, s["s"]*s["n"]**2
    M = (s["r"] + 1)*Y
    Q = U*M**2
    baseline.need([EQUATION_LABELS[i] for i in (7, 10, 11)] == ["E9", "E11", "E12"],
                  "the three changed source equations")
    source[7] = Q*(Q + 1)*s["k"]**2 - s["tau"]*(s["tau"] + 1)
    source[10] = s["k"] - s["h"]*(s["r"] + 1)
    source[11] = s["a"] - M*(U + 1)
    return source


def verify_support_bounds():
    return previous.verify_support_bounds()


def verify_certificate():
    receipt = previous.verify_certificate()
    support = verify_support_bounds()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A = s["a"]
    G_source = 1 + (A + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (A + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**2*(s["n"]**2 - 1),
        16: source[15]*(A + 1)*(G_source + G_calculated)*H17**2,
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 equality tests")
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
    U, Y = s["w"]*s["n"]**2, s["s"]*s["n"]**2
    M = (s["r"] + 1)*Y
    Q = U*M**2
    for name, expected in {"rsn2": M, "UM": U*M, "wsq": Q,
                           "R12": M*(U + 1), "hpm1": s["h"]*(s["r"] + 1)}.items():
        baseline.need(sp.expand(env[name] - expected) == 0, "exact changed register " + name)
    primitives, primitive_histogram = previous.verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 106 and primitive_histogram == {"+": 47, "*": 59},
                  "106-operation core histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {operand for pair in EQUALITIES for operand in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    baseline.need("R11" not in used and "R11" not in env, "the old addition is unused and absent")
    numeral_env = {}
    numeral_histogram = baseline.run_schedule(NUMERAL_SCHEDULE, numeral_env)
    for value, register in LITERAL_REGISTERS.items():
        baseline.need(numeral_env[register] == value, "all fixed numerals are constructed")
    numeral_primitives, numeral_primitive_histogram = previous.verify_primitives(
        NUMERAL_SCHEDULE, numeral_env)
    baseline.need(len(numeral_primitives) == 6 and
                  numeral_primitive_histogram == {"+": 1, "*": 5}, "six numeral operations")
    strict_env = dict(SYM)
    strict_histogram = baseline.run_schedule(STRICT_SCHEDULE, strict_env)
    strict_primitives, strict_primitive_histogram = previous.verify_primitives(STRICT_SCHEDULE, strict_env)
    baseline.need(len(strict_primitives) == 112 and
                  strict_primitive_histogram == {"+": 48, "*": 64}, "explicit strict112 certificate")
    baseline.need({operand for _, _, left, right in STRICT_SCHEDULE
                   for operand in (left, right) if isinstance(operand, int)} == {1},
                  "strict instructions only use the literal one")
    for name in env:
        baseline.need(sp.expand(strict_env[name] - env[name]) == 0,
                      "strict and core values agree exactly")
    receipt.update({
        "operations": 106, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 47, "multiplications": 59},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": support,
        "reparameterized_inputs": {
            "tau": "positive half-root (chi_P(r+1)-1)/2",
            "h": "positive quotient k/(r+1); P-1 is divisible by r+1",
            "M": "(r+1)*s*n^2, computed by register rsn2; not an additional input",
            "Q": "w*(r+1)^2*s^2*n^6=U*M^2, already register wsq; not an extra input",
            "P": "mathematical Pell parameter 2*Q+1; not computed by any instruction",
            "a": "main Pell parameter A=M*(U+1), with M=(r+1)*Y",
        },
        "exact_witness_identities": [
            "(2*tau+1)^2-1=4*tau*(tau+1)",
            "P-1=2*U*(r+1)^2*Y^2 is divisible by r+1",
            "at the recovered index r+1, k=psi_P(r+1) is divisible by r+1",
        ],
        "numerals_from_one": {"operations": 6, "histogram": numeral_histogram,
            "primitive_instructions": numeral_primitives,
            "scope": "Generate 2,4,L from 1; x,Z,V,H remain supplied parameters"},
        "operations_with_numerals_from_one": 112,
        "strict_certificate": {"operations": 112, "straight_line_histogram": strict_histogram,
            "additions_and_multiplications_only": {"additions": 48, "multiplications": 64},
            "primitive_instructions": strict_primitives, "equalities": EQUALITIES,
            "only_literal": 1},
        "proofs": receipt["proofs"] + ["../1980/BASE_TWO_INDEX_MULTIPLE_PROOF.md"],
        "scope": "106 core operations for the base-two index-multiple system; 112 operations including all fixed numeral constructions",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"],
          ";", result["operations_with_numerals_from_one"], "with numerals from 1")
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
