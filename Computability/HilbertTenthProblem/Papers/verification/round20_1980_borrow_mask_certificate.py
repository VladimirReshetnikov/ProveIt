#!/usr/bin/env python3
"""103-operation certificate with a borrow-tolerant target encoding.

The separate proof is SINGLE_OFFSET_ENCODING_PROOF.md.
The low B*lambda offset is deleted from S3. Ordinary target polynomials
become 4F+delta^2, while the special target remains delta^2.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round19_1980_shared_ratio_product_certificate as previous
from round13_1980_certificate import verify_primitives, verify_support_bounds

HERE = Path(__file__).resolve().parent
OUT = HERE / "round20_1980_borrow_mask_certificate.json"
L, K = previous.L, previous.K
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "qp1":
            baseline.need((operation, left, right) == ("+", "q", 1),
                          "remove exactly the q+1 addition")
            continue
        if target == "P2":
            baseline.need((operation, left, right) == ("*", "Lam", "qp1"),
                          "replace the low-offset baseline by B*lambda*q")
            right = "q"
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 103, "one addition disappears globally")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    B = s["H"]*s["b"]**2
    C = s["x"] + s["g"]
    Y = s["l"] + s["e"]*s["q"]
    S3 = (2*s["e"] - s["Z"]*s["la"])*C**2 + B*s["la"]*s["q"]
    S = s["g"] + s["q"]**2*(Y + s["q"]**2*S3)
    Tplus = (s["q"]**2 - (s["b"] - 1)*s["l"]
             + s["th"]*s["la"]*s["q"]**2
             + (B - 4)*s["l"]*s["q"]**4)
    baseline.need(EQUATION_LABELS[6] == "E7", "the packed index equation")
    source[6] = s["r"] - S*(s["n"]**2 - s["n"]) - Tplus*(s["n"]**2 - 1)
    baseline.need(EQUALITIES[20] == ("S3", "sigma"), "the positive coefficient block")
    source[20] = S3 - s["sigma"]
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
    B = s["H"]*s["b"]**2
    old_source = previous.source_residuals()
    for index, residual in enumerate(old_source):
        change = (B*s["la"]*s["q"]**4*(s["n"]**2 - s["n"]) if index == 6
                  else -B*s["la"] if index == 20 else sp.Integer(0))
        baseline.need(sp.expand(source[index] - residual - change) == 0,
                      "only the two S3-dependent source equations change")
    baseline.need(sp.expand(env["P2"] - B*s["la"]*s["q"]) == 0,
                  "the new high baseline is exactly B*lambda*q")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 103 and primitive_histogram == {"+": 46, "*": 57},
                  "103-operation histogram with fixed numerals free")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every positive input participates")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    baseline.need("qp1" not in used and "qp1" not in env,
                  "the q+1 register is absent globally")
    receipt.update({
        "status": "PASS",
        "operations": 103, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 46, "multiplications": 57},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": verify_support_bounds(),
        "input_admissibility": {
            "ordinary_targets": "4*F_homogeneous+delta^2, including the input guard",
            "special_target": "delta^2",
            "quadratic_rows": "1830 homogenized basis rows, guard u*delta-x^2, and special delta^2",
            "coefficient_polynomial": "D has target coefficient G_I/c_I at t_I-weight(I), where c_I is 1 for squares and 2 for cross terms",
            "centering": "z is a power of two >=2 strictly exceeding every absolute coefficient of the new D; Z=2z",
            "support_code": "ell_0(B)=sum(60 positive coordinate powers)+sum(1832 row powers); unit input excluded",
            "coefficient_code": "e_0(B)=z*sum(B^j,j=0..K-1)+D(B)",
            "packed_index": "V=ell_0(Z)+e_0(Z)*Z^L",
            "radix_scale": "H a power of two >max(2*Z^(2L+1),4^(t_last+3)*Z*1900^2,3L,16)",
            "packing": "same row and variable positions as round19; fixed Z,V,H are rebuilt from the new D",
            "scope": "fixed numerals and index parameters have no arithmetic cost",
        },
        "proofs": receipt["proofs"] + ["../1980/SINGLE_OFFSET_ENCODING_PROOF.md",
                                         "../1980/HIGH_MASK_SINGLE_OFFSET_PROOF.md"],
        "fixed_index_override": "SINGLE_OFFSET_ENCODING_PROOF.md rebuilds D,z,Z,V,H with the same modular support and exponent L; it supersedes the older coefficient targets",
        "scope": "103 arithmetic operations with the borrow-tolerant target encoding; the independent mathematical proof establishes membership equivalence",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], result["operations"], result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", len(result["equalities"]), "equalities")
