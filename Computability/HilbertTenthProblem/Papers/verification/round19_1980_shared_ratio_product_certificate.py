#!/usr/bin/env python3
"""104 operations: share UY and Yk in the first Pell norm.

Q(Q+1)k^2=((UY)^2+U)(Yk)^2 for Q=UY^2. The interval already needs
Yk, and UY is already used for a0=UY+Y. Replacing the index modulus
Q by UY removes its last separate use; the exact-index argument and
positive witness maps are in PELL_SHARED_RATIO_PRODUCT_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round18_1980_unit_scale_certificate as previous
from round13_1980_certificate import verify_primitives, verify_support_bounds

HERE = Path(__file__).resolve().parent
OUT = HERE / "round19_1980_shared_ratio_product_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    schedule = []
    removed = {"wsq", "Qplus1", "QQplus1", "k2", "L9", "ksn2"}
    expected = {
        "wsq": ("*", "UM", "sn2"),
        "Qplus1": ("+", "wsq", 1),
        "QQplus1": ("*", "wsq", "Qplus1"),
        "k2": ("*", "k", "k"),
        "L9": ("*", "QQplus1", "k2"),
        "ksn2": ("*", "k", "sn2"),
    }
    for target, operation, left, right in previous.SCHEDULE:
        if target in removed:
            baseline.need((operation, left, right) == expected[target],
                          "the old norm/interval block is identified exactly")
            if target == "wsq":
                schedule.extend([
                    ("ksn2", "*", "k", "sn2"),
                    ("UM2", "*", "UM", "UM"),
                    ("scaled_norm_coefficient", "+", "UM2", "wn2"),
                    ("ratio_product2", "*", "ksn2", "ksn2"),
                    ("L9", "*", "scaled_norm_coefficient", "ratio_product2"),
                ])
            continue
        if target == "hpm1":
            baseline.need((operation, left, right) == ("*", "h", "wsq"),
                          "the last use of Q was the index quotient")
            right = "UM"
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 104, "one multiplication is removed globally")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    D = s["w"]*s["s"]*s["n"]**4
    baseline.need(EQUATION_LABELS[10] == "E11", "the changed index equation")
    source[10] = s["k"] - s["r"] - 1 - s["h"]*D
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
    U, Y = s["w"]*s["n"]**2, s["s"]*s["n"]**2
    D, Q = U*Y, U*Y**2
    for name, expected_value in {
        "UM": D, "ksn2": Y*s["k"], "scaled_norm_coefficient": D**2 + U,
        "L9": Q*(Q + 1)*s["k"]**2, "hpm1": s["h"]*D,
    }.items():
        baseline.need(sp.expand(env[name] - expected_value) == 0,
                      "exact shared-factor register " + name)
    old_source = previous.source_residuals()
    for index, residual in enumerate(old_source):
        if index != 10:
            baseline.need(sp.expand(source[index] - residual) == 0,
                          "only E11 changes as a source polynomial")
    baseline.need(sp.expand(source[10].subs(s["h"], s["h"]*Y) - old_source[10]) == 0,
                  "exact forward index-witness map h_new=Y*h_old")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 104 and primitive_histogram == {"+": 47, "*": 57},
                  "104-operation core histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    baseline.need(not ({"wsq", "Qplus1", "QQplus1", "k2"} & (used | set(env))),
                  "the discarded Q and norm registers are absent globally")
    receipt.update({
        "operations": 104, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 47, "multiplications": 57},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": verify_support_bounds(),
        "reparameterized_inputs": receipt["reparameterized_inputs"] | {
            "h": "positive quotient (k-r-1)/(UY); forward map h_new=Y*h_old; exact index gives positive reverse map h_old=h_new/Y",
            "Q": "mathematical UY^2 only; no computed Q register is needed",
            "D": "UY, existing register UM, used as the first Pell index modulus",
        },
        "exact_witness_identities": [
            "Q(Q+1)k^2=((UY)^2+U)(Yk)^2, with Q=UY^2",
            "E11_new(h_new=Y*h_old)=E11_old",
            "the recovered exact index implies h_new is a positive multiple of Y",
        ],
        "proofs": receipt["proofs"] + ["../1980/PELL_SHARED_RATIO_PRODUCT_PROOF.md"],
        "scope": "104 core operations by sharing UY and Yk in the first Pell norm and weakening the index modulus to UY; all fixed numerals supplied free",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
