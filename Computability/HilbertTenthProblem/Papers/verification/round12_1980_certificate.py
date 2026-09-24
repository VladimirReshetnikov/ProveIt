#!/usr/bin/env python3
"""107 operations: compose the positive coefficient bound and odd Pell root.

Q=UM^2 is already the register wsq. For the unchanged mathematical Pell
parameter P=2Q+1, replace tau_old by 2*tau+1 and impose
tau*(tau+1)=Q*(Q+1)*k^2. Replace k=r+1+h*(2Q) by k=r+1+h*Q.
The exact-index argument in PELL_ODD_ROOT_PROOF.md proves that this
weaker congruence still forces h to be even, so both positive witness
maps are valid. No parity or division instruction is left uncounted.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round10_1980_certificate as previous
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round12_1980_certificate.json"
L = previous.L
K = previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    schedule = list(previous.SCHEDULE)
    baseline.need(len(schedule) == 108, "108-operation predecessor")
    replace_block(schedule, ["R8", "Pplus1", "p2m1", "k2", "P9", "L9", "R9"], [
        ("Qplus1", "+", "wsq", 1),
        ("QQplus1", "*", "wsq", "Qplus1"),
        ("k2", "*", "k", "k"),
        ("L9", "*", "QQplus1", "k2"),
        ("tauplus1", "+", "tau", 1),
        ("R9", "*", "tau", "tauplus1"),
    ])
    replace_block(schedule, ["hpm1"], [("hpm1", "*", "h", "wsq")])
    baseline.need(all("R8" not in row for row in schedule), "2Q is no longer computed")
    baseline.need(len(schedule) == 107, "107-operation odd-root schedule")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    Q = s["w"]*s["r"]**2*s["s"]**2*s["n"]**6
    baseline.need(EQUATION_LABELS[7] == "E9" and EQUATION_LABELS[10] == "E11",
                  "explicit positions of the changed Pell equations")
    source[7] = Q*(Q + 1)*s["k"]**2 - s["tau"]*(s["tau"] + 1)
    source[10] = s["k"] - s["r"] - 1 - s["h"]*Q
    return source


def verify_certificate():
    receipt = previous.verify_certificate()
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
    baseline.need(len(source) == len(EQUALITIES) == len(EQUATION_LABELS) == 22,
                  "22 source equations and equality tests")
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
        baseline.need(operation in primitive_histogram, "only addition and multiplication")
        result = left + right if operation == "+" else left*right
        baseline.need(sp.expand(result - target) == 0, "serialized primitive identity")
        primitive_histogram[operation] += 1
    old_source = previous.source_residuals()
    baseline.need(sp.expand(old_source[7].subs(s["tau"], 2*s["tau"] + 1)
                            - 4*source[7]) == 0, "exact odd-root norm identity")
    baseline.need(sp.expand(source[10].subs(s["h"], 2*s["h"])
                            - old_source[10]) == 0, "exact forward congruence witness map")
    Q = s["w"]*s["r"]**2*s["s"]**2*s["n"]**6
    baseline.need(sp.expand(env["wsq"] - Q) == 0, "existing register is exactly Q=UM^2")
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    baseline.need(len(primitives) == sum(histogram.values()) == 107, "107 arithmetic instructions")
    baseline.need(primitive_histogram == {"+": 48, "*": 59}, "final primitive histogram")
    receipt.update({
        "operations": 107, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 48, "multiplications": 59},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "reparameterized_inputs": {
            "tau": "positive half-root: tau_old=2*tau+1",
            "h": "k=r+1+h*Q; necessity h_new=2*h_old; sufficiency proves h_new is even",
            "Q": "w*r^2*s^2*n^6=U*M^2, already register wsq; not an extra input",
            "P": "mathematical Pell parameter2*Q+1; not computed by any instruction",
        },
        "exact_witness_identities": [
            "E9_old(tau_old=2*tau_new+1)=4*E9_new",
            "E11_new(h_new=2*h_old)=E11_old",
        ],
        "proofs": receipt["proofs"] + ["../1980/PELL_ODD_ROOT_PROOF.md",
                                         "../1980/COMPOSED_107_PROOF.md"],
        "operations_with_numerals_from_one": 107 + receipt["numerals_from_one"]["operations"],
        "scope": "positive coefficient bound and unit-position homogeneous packing; factored odd Pell root and halved index modulus",
    })
    return receipt


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive unknowns")
    print("Including fixed numeral construction:", receipt["operations_with_numerals_from_one"])
