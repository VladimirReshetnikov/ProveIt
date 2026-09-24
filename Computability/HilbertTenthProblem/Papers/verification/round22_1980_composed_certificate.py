#!/usr/bin/env python3
"""102 operations: combine borrow-tolerant targets with a common Pell witness.

Retain U=w*n^2 and the index modulus UY. Reuse U as the base-four
exponential witness W, deleting the separate product b*w. The full
composition proof is COMPOSED_102_PROOF.md; fixed numerals are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round19_1980_shared_ratio_product_certificate as ancestor
import round20_1980_borrow_mask_certificate as previous
from round13_1980_certificate import verify_primitives, verify_support_bounds

HERE = Path(__file__).resolve().parent
OUT = HERE / "round22_1980_composed_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def common_witness_schedule(source_schedule):
    schedule = []
    removed = 0
    for target, operation, left, right in source_schedule:
        if target == "bw":
            baseline.need((operation, left, right) == ("*", "b", "w"),
                          "the exponential witness is now the existing register U=w*n^2")
            removed += 1
            continue
        left = "wn2" if left == "bw" else left
        right = "wn2" if right == "bw" else right
        schedule.append((target, operation, left, right))
    baseline.need(removed == 1, "exactly one exponential-witness multiplication disappears")
    return schedule


SCHEDULE = common_witness_schedule(previous.SCHEDULE)


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    U = s["w"]*s["n"]**2
    baseline.need(EQUATION_LABELS[13] == "E14", "the changed exponent congruence")
    source[13] = s["d"] - U - s["c"]*s["a"] - s["ga"]*(8*s["a"] + 15)
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
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 source equations and equality tests")
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
    for name, expected_value in {
        "wn2": U, "UM": U*Y, "hpm1": s["h"]*U*Y,
        "R12": Y*(U + 1), "D1": U + s["c"]*s["a"],
    }.items():
        baseline.need(sp.expand(env[name] - expected_value) == 0,
                      "exact common-witness register " + name)
    for index, residual in enumerate(previous.source_residuals()):
        change = s["w"]*(s["b"] - s["n"]**2) if index == 13 else sp.Integer(0)
        baseline.need(sp.expand(source[index] - residual - change) == 0,
                      "only E14 changes relative to the borrow-mask system")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 102 and primitive_histogram == {"+": 46, "*": 56},
                  "102-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    baseline.need(not ({"bw", "qp1"} & (used | set(env))),
                  "the separate exponential product and low-offset addition are absent")
    reverse_schedule = [
        (target, operation, left, "q" if target == "P2" else right)
        for target, operation, left, right in common_witness_schedule(ancestor.SCHEDULE)
        if target != "qp1"
    ]
    baseline.need(SCHEDULE == reverse_schedule, "both orders give the same complete schedule")
    reverse_source = list(ancestor.source_residuals())
    B = s["H"]*s["b"]**2
    reverse_source[13] += s["w"]*(s["b"] - s["n"]**2)
    reverse_source[6] += B*s["la"]*s["q"]**4*(s["n"]**2 - s["n"])
    reverse_source[20] -= B*s["la"]
    baseline.need(all(sp.expand(left - right) == 0 for left, right in zip(source, reverse_source)),
                  "both orders give the same complete source system")
    receipt.update({
        "status": "PASS",
        "operations": 102, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 46, "multiplications": 56},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": verify_support_bounds(),
        "reparameterized_inputs": receipt["reparameterized_inputs"] | {
            "U": "w*n^2, existing register wn2, shared with exponential witness W",
            "W": "the same value as U, without a separate product",
            "w": "positive quotient 4^(2*r+1)/n^2",
        },
        "proofs": receipt["proofs"] + ["../1980/PELL_COMMON_WITNESS_PROOF.md",
                                         "../1980/COMPOSED_102_PROOF.md"],
        "composition_checks": {"schedule_commutes": True, "all_source_residuals_commute": True,
                               "removed_registers": ["qp1", "bw"],
                               "fixed_index": "new borrow-tolerant coefficient code from round20"},
        "scope": "102 arithmetic operations combining borrow-tolerant targets and the common Pell/exponential witness U=w*n^2; fixed numerals free; positive-domain composition proved independently",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], result["operations"], result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
