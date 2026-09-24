#!/usr/bin/env python3
"""94 operations by shifting the fixed affine-radix component by four.

SHIFTED_AFFINE_94_PROOF.md gives the exact positive-witness bijection.
The register theta_sum stores theta=H+b; the actual radix is H+b+4.
Fixed numerals and equality tests are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round32_1980_affine_radix_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round33_1980_shifted_affine_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
baseline.need(EQUALITIES[3] == ("L3", "B"), "the old radix equality")
EQUALITIES[3] = ("th", "theta_sum")


def make_schedule():
    result = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "L3":
            baseline.need((operation, left, right) == ("+", "th", 4),
                          "remove exactly theta plus four")
            continue
        baseline.need(left not in ("B", "L3") and right not in ("B", "L3"),
                      "neither old radix register has a downstream arithmetic use")
        result.append(("theta_sum" if target == "B" else target,
                       operation, left, right))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    h = SYM["H"]
    return [residual.subs(h, h+4) for residual in previous.source_residuals()]


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B_math = s["a"]+4, s["H"]+s["b"]+4
    D = A*A-1
    K_source, K_calculated = D*(s["f"]**2-1), env["ic22"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: -source[15]*(K_source+K_calculated-1)*H17**2,
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B_math))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22,
                  "22 complete source equations and equality tests")
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual-residual-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError("residual mismatch at " + EQUATION_LABELS[index])
        records.append({"equation": EQUATION_LABELS[index], "equality": [left, right],
                        "source_residual_polynomial": sp.sstr(sp.expand(residual)),
                        "certificate_residual_polynomial": sp.sstr(actual),
                        "source_residual_sign": sign,
                        "triangular_correction_polynomial": sp.sstr(sp.expand(correction))})
    for index in (3, 15):
        baseline.need(records[index]["triangular_correction_polynomial"] == "0",
                      "each correction has an independently exact prerequisite")
    old_source = previous.source_residuals()
    changed = []
    for index, residual in enumerate(source):
        baseline.need(sp.expand(residual-old_source[index].subs(s["H"], s["H"]+4)) == 0,
                      "exact source substitution H_old = H_new + four")
        if sp.expand(residual-old_source[index]) != 0:
            changed.append(index)
    baseline.need(changed == [2, 3, 17], "only the three radix-dependent source rows change")
    baseline.need(sp.expand(source[3]-(s["th"]-s["H"]-s["b"])) == 0,
                  "the new radix equation is theta = H+b")
    baseline.need(env["theta_sum"] == s["H"]+s["b"],
                  "theta_sum stores theta, not the mathematical radix")
    old_env = dict(SYM)
    old_env["H"] = s["H"]+4
    baseline.run_schedule(previous.SCHEDULE, old_env)
    for name, value in env.items():
        if name not in ("H", "theta_sum"):
            baseline.need(sp.expand(value-old_env[name]) == 0,
                          "every retained non-radix register has the same value")
    baseline.need(sp.expand(old_env["B"]-env["theta_sum"]-4) == 0,
                  "the old B register exceeds theta_sum by exactly four")
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 94 and counts == {"+": 43, "*": 51},
                  "94-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  "34 positive unknowns and four inputs")
    baseline.need("L3" not in env and "L3" not in used,
                  "the deleted addition has no remaining use")
    baseline.need("B" not in env and "B" not in used,
                  "the old radix register is renamed without remaining uses")
    baseline.need(sum("theta_sum" in (left, right)
                      for _, _, left, right in SCHEDULE) == 0
                  and sum("theta_sum" in pair for pair in EQUALITIES) == 1,
                  "theta_sum is used only in its single equality test")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    return {
        "status": "PASS", "operations": 94,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 43, "multiplications": 51},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": changed,
        "fixed_index": "H=H0-3>0, where H0 is the large power of two from the affine95 index; V and Tindex are unchanged",
        "parameter_bijection": "H_old=H_new+4; all 34 positive witnesses and queried x are unchanged",
        "register_semantics": {"theta_sum": "H+b=theta", "actual_radix": "H+b+4=H0+b+1"},
        "proofs": ["../1980/SHIFTED_AFFINE_94_PROOF.md", "../1980/AFFINE_RADIX_95_PROOF.md"],
        "scope": "complete94-operation certificate, exact parameter substitution and positive-witness bijection; fixed numerals and equality tests free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
