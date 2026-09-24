#!/usr/bin/env python3
"""103 core operations: share U=B*w with the exponential witness W.

The first index modulus becomes the existing coefficient U*(Q+1), Q=U*Y^2.
The packed index R is even before Pell decoding; this supplies the odd
index needed for the congruence modulo Q+1. PELL_SHARED_EXPONENT_PROOF.md
reproves the exact index, exponent order and positive witness construction.
All fixed numerals are supplied free. No predecessor is edited.
"""
from __future__ import annotations

import json
from itertools import product
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round19_1980_shared_ratio_product_certificate as previous
from round13_1980_certificate import verify_primitives, verify_support_bounds

HERE = Path(__file__).resolve().parent
OUT = HERE / "round21_1980_shared_exponent_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "wn2":
            baseline.need((operation, left, right) == ("*", "w", "n2"),
                          "replace the old binomial scale by U=Bw")
            right = "B"
        if target == "bw":
            baseline.need((operation, left, right) == ("*", "b", "w"),
                          "the exponential witness is now the same register U")
            continue
        if target == "hpm1":
            baseline.need((operation, left, right) == ("*", "h", "UM"),
                          "replace the first index modulus by the existing norm coefficient")
            right = "scaled_norm_coefficient"
        left = "wn2" if left == "bw" else left
        right = "wn2" if right == "bw" else right
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 103, "one exponential-witness multiplication disappears")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    B = s["H"]*s["b"]**2
    U, Y = B*s["w"], s["s"]*s["n"]**2
    Q = U*Y**2
    baseline.need([EQUATION_LABELS[i] for i in (7, 10, 11, 13)]
                  == ["E9", "E11", "E12", "E14"], "four changed source equations")
    source[7] = Q*(Q + 1)*s["k"]**2 - s["tau"]*(s["tau"] + 1)
    source[10] = s["k"] - s["r"] - 1 - s["h"]*U*(Q + 1)
    source[11] = s["a"] - Y*(U + 1)
    source[13] = s["d"] - U - s["c"]*s["a"] - s["ga"]*(8*s["a"] + 15)
    return source


def verify_packing_parity():
    support = verify_support_bounds()
    baseline.need(min(support["variable_weights"]) >= 1
                  and int(support["first_row_weight"]) >= 1 and L >= 1,
                  "the fixed index V is even because every term has a positive power of even Z")
    checked = 0
    for q, b, ell, e, S in product(range(2), repeat=5):
        if (ell + e*q) % 2:
            continue
        # B, theta and V are even. Work entirely in residue representatives.
        N = q**8
        Tplus = q**2 - (b - 1)*ell - 4*ell*q**4
        R = S*(N**2 - N) + Tplus*(N**2 - 1)
        baseline.need(R % 2 == 0, "every compatible residue pattern forces R even")
        checked += 1
    baseline.need(checked == 16, "all compatible parity patterns were checked")
    return {"compatible_patterns_checked": checked,
            "admissibility": "Z and H are even; every support weight and L is positive, so V is even",
            "equations": "theta=B-Z and ell+e*q=V+t*theta make the packed middle value even",
            "conclusion": "R is even before either exponential relation or Pell decoding"}


def verify_certificate():
    receipt = previous.verify_certificate()
    parity = verify_packing_parity()
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
    B = s["H"]*s["b"]**2
    U, Y = B*s["w"], s["s"]*s["n"]**2
    Q = U*Y**2
    for name, expected_value in {
        "wn2": U, "UM": U*Y, "scaled_norm_coefficient": U*(Q + 1),
        "L9": Q*(Q + 1)*s["k"]**2,
        "hpm1": s["h"]*U*(Q + 1), "R12": Y*(U + 1),
        "D1": U + s["c"]*s["a"],
    }.items():
        baseline.need(sp.expand(env[name] - expected_value) == 0,
                      "exact shared-exponent register " + name)
    for index, residual in enumerate(previous.source_residuals()):
        if index not in {7, 10, 11, 13}:
            baseline.need(sp.expand(source[index] - residual) == 0,
                          "all other source polynomials are unchanged")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 103 and primitive_histogram == {"+": 47, "*": 56},
                  "103-operation core histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    baseline.need("bw" not in env and "bw" not in used, "the separate exponential product is absent")
    receipt.update({
        "operations": 103, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 47, "multiplications": 56},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "packing_parity": parity,
        "reparameterized_inputs": {
            "tau": "positive half-root (chi_P(r+1)-1)/2",
            "h": "positive quotient (k-r-1)/(U*(Q+1)); integrality uses odd r+1 and coprime U,Q+1",
            "U": "B*w, existing register wn2, shared with the exponential witness W",
            "Y": "s*n^2, existing register sn2",
            "M": "Y; not an additional input or computed register",
            "Q": "mathematical U*Y^2 only; no computed Q register",
            "P": "mathematical 2*Q+1; no computed P register",
            "index_modulus": "U*(Q+1)=(UY)^2+U, existing scaled_norm_coefficient",
            "a": "positive a0=Y*(U+1), mathematical main Pell parameter A=a0+4",
            "w": "positive quotient 4^(2*r+1)/B, where B=H*b^2",
        },
        "exact_witness_identities": [
            "Q(Q+1)k^2=((UY)^2+U)(Yk)^2, with Q=UY^2",
            "psi_P(t)=t modulo U because P=1 modulo U",
            "psi_P(t)=(-1)^(t-1)*t modulo Q+1 because P=-1 modulo Q+1",
            "gcd(U,Q+1)=1 and odd t=r+1 give divisibility by U*(Q+1)",
        ],
        "proofs": receipt["proofs"] + ["../1980/PELL_SHARED_EXPONENT_PROOF.md"],
        "scope": "103 core operations by sharing U=Bw with the exponential witness and using the already computed norm coefficient as index modulus; all fixed numerals supplied free",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations", result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
