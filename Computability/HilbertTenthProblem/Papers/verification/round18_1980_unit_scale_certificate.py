#!/usr/bin/env python3
"""105 operations: reuse Y as M in the base-four Pell construction.

The packed index satisfies R<2N^3. That upper bound makes M=Y sufficient
for the pre-exponent estimates; the larger ratio error is bounded only
after bw=4^(2R+1) is decoded. See PELL_UNIT_SCALE_PROOF.md. This version
retains the old first-Pell congruence and is independent of round16.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round14_1980_base_four_certificate as previous
from round13_1980_certificate import verify_primitives, verify_support_bounds

HERE = Path(__file__).resolve().parent
OUT = HERE / "round18_1980_unit_scale_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "rsn2":
            baseline.need((operation, left, right) == ("*", "r", "sn2"),
                          "the sole deleted multiplication computes M=RY")
            continue
        left = "sn2" if left == "rsn2" else left
        right = "sn2" if right == "rsn2" else right
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 105, "one scale multiplication is eliminated")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    U, Y = s["w"]*s["n"]**2, s["s"]*s["n"]**2
    Q = U*Y**2
    baseline.need([EQUATION_LABELS[i] for i in (7, 10, 11)] == ["E9", "E11", "E12"],
                  "the three changed source equations")
    source[7] = Q*(Q + 1)*s["k"]**2 - s["tau"]*(s["tau"] + 1)
    source[10] = s["k"] - s["r"] - 1 - s["h"]*Q
    source[11] = s["a"] - Y*(U + 1)
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
    Q = U*Y**2
    for name, expected in {
        "sn2": Y, "UM": U*Y, "wsq": Q,
        "R12": Y*(U + 1), "hpm1": s["h"]*Q,
    }.items():
        baseline.need(sp.expand(env[name] - expected) == 0, "exact changed register " + name)
    for index, residual in enumerate(previous.source_residuals()):
        if index not in {7, 10, 11}:
            baseline.need(sp.expand(source[index] - residual) == 0,
                          "all other source polynomials are unchanged")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 105 and primitive_histogram == {"+": 47, "*": 58},
                  "105-operation core histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    baseline.need("rsn2" not in env and "rsn2" not in used,
                  "the old scale multiplication is absent everywhere")
    N = sp.Symbol("N", positive=True, integer=True)
    baseline.need(sp.expand((N - 1)*(N**2 - N) + N*(N**2 - 1)
                            - (2*N**3 - 2*N**2)) == 0,
                  "exact upper bound for the packed index")
    for key in ("numerals_from_one", "operations_with_numerals_from_one", "strict_certificate"):
        receipt.pop(key, None)
    receipt.update({
        "operations": 105, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 47, "multiplications": 58},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": verify_support_bounds(),
        "reparameterized_inputs": {
            "tau": "positive half-root (chi_P(r+1)-1)/2",
            "h": "positive quotient (k-r-1)/Q; the old index congruence is retained",
            "M": "Y=s*n^2, reusing register sn2; not an additional input",
            "Q": "U*Y^2=w*s^2*n^6, already register wsq; not an extra input",
            "P": "mathematical Pell parameter 2*Q+1; not computed by any instruction",
            "a": "positive a0=Y*(U+1), mathematical main Pell parameter A=a0+4",
            "w": "the base-four exponent congruence forces b*w=4^(2*r+1)",
        },
        "exact_witness_identities": [
            "tau_old=2*tau+1 gives the ordinary Pell norm with P=2*Q+1",
            "h=(psi_P(r+1)-r-1)/Q is positive integral by the Pell congruence",
        ],
        "packing_upper_bound": "R<=2*N^3-2*N^2<2*N^3 before either exponent relation",
        "proofs": receipt["proofs"] + ["../1980/PELL_UNIT_SCALE_PROOF.md"],
        "scope": "105 core operations by reusing Y as M; all fixed numerals supplied free; an independent alternative to the index-multiple certificate",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
