#!/usr/bin/env python3
"""100 operations: halve the coefficient and share the theta-lambda offset.

The companion HALF_CENTER_ENCODING_PROOF.md supplies the changed fixed
index, positive-domain equivalence, and all bootstrap arguments. Fixed
numerals are free. This file verifies the complete arithmetic certificate.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round23_1980_fixed_four_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round25_1980_half_center_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
EQUALITIES[2] = ("q2", "R2")


def make_schedule():
    removed_names = {"L2", "Lam", "R2", "zl", "twice_e", "t2", "Tcoef", "P2"}
    replacement = [
        ("theta_lambda", "*", "th", "la"),
        ("twice_lambda", "*", 2, "la"),
        ("Tcoef", "+", "theta_lambda", 1),
        ("three_lambda", "+", "twice_lambda", "la"),
        ("R2", "+", "Tcoef", "three_lambda"),
        ("t2", "-", "twice_lambda", "e"),
        ("P2", "*", "theta_lambda", "q"),
    ]
    schedule = []
    removed = []
    for instruction in previous.SCHEDULE:
        target = instruction[0]
        if target == "L2":
            schedule.extend(replacement)
        if target in removed_names:
            removed.append(target)
        else:
            schedule.append(instruction)
    baseline.need(set(removed) == removed_names and len(removed) == 8,
                  "seven shared instructions replace exactly eight")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    q, n = s["q"], s["n"]
    C = s["x"] + s["g"]
    coefficient = 2*s["la"] - s["e"]
    S3 = s["th"]*s["la"]*q - coefficient*C**2
    S2 = s["l"] + s["e"]*q
    S = s["g"] + q**2*(S2 + q**2*S3)
    Tplus = (q**2*(1+s["th"]*s["la"])
             - (s["b"]-1)*s["l"] + s["th"]*s["l"]*q**4)
    source[6] = s["r"] - S*(n**2-n) - Tplus*(n**2-1)
    source[20] = S3 - s["sigma"]
    source[21] = coefficient - s["Omega"]
    return source


def verify_target_forms():
    x, u, v, y, w, delta = sp.symbols("x u v y w delta")
    coordinates = [x, delta, u, v, y, w]
    paired = {
        "product": u*v-w*delta,
        "sum": (u+v-w)*delta,
        "copy": (u-v)*delta,
        "zero": u*delta,
    }
    rows = {f"{name}_{sign:+d}": sign*row
            for name, row in paired.items() for sign in (-1, 1)}
    rows.update({"unit_lower": u*delta-delta**2,
                 "unit_boolean": u*delta-u**2,
                 "guard": y*delta-x**2})
    records = []
    for name, residual in rows.items():
        target = sp.Poly(2*residual+delta**2, *coordinates)
        coefficients = []
        for monomial, coefficient in target.terms():
            baseline.need(sum(monomial) == 2, "homogeneous target")
            multinomial = 1 if 2 in monomial else 2
            divided = coefficient/multinomial
            baseline.need(divided in {-2, -1, 0, 1}, "fixed-four alphabet")
            coefficients.append(int(divided))
        records.append({"name": name, "residual": sp.sstr(residual),
                        "D_coefficients": coefficients})
    for value in range(-20, 21):
        for carry in (-1, 0):
            baseline.need((0 <= 2*value+1+carry <= 3) == (value in (0, 1)),
                          "one ordinary row encodes zero or one")
            for opposite_carry in (-1, 0):
                both = (0 <= 2*value+1+carry <= 3
                        and 0 <= -2*value+1+opposite_carry <= 3)
                baseline.need(both == (value == 0), "paired rows force zero")
    for value in range(20):
        baseline.need((0 <= value*value <= 3) == (value in (0, 1)),
                      "first special row has no incoming carry")
        baseline.need(((value-1 in (0, 1)) and (value-value*value in (0, 1)))
                      == (value == 1), "two unit rows force one")
    return {"coefficient_alphabet": [-2, -1, 0, 1], "rows": records,
            "special_target": "delta^2 is first, with incoming carry zero",
            "scope": "symbolic target identities and finite carry regressions; universal compilation and carry arguments are in the separate proof"}


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    G_source = 1+(A+1)*(s["f"]**2-1)
    G_calculated = 1+(A+1)*env["AE"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: source[15]*(A+1)*(G_source+G_calculated)*H17**2,
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B))),
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 source equations and tests")
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
    for index, old in enumerate(previous.source_residuals()):
        if index not in (6, 20, 21):
            baseline.need(sp.expand(source[index]-old) == 0,
                          "unchanged source equation " + EQUATION_LABELS[index])
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 100 and primitive_histogram == {"+": 45, "*": 55},
                  "100-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 100, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 45, "multiplications": 55},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "normal_form_checks": verify_target_forms(),
        "support_checks": previous.verify_dynamic_support(),
        "proofs": ["../1980/HALF_CENTER_ENCODING_PROOF.md",
                   "../1980/FIXED_FOUR_ENCODING_PROOF.md",
                   "../1980/PELL_COMMON_WITNESS_PROOF.md"],
        "scope": "exact 100-instruction arithmetic certificate, with fixed numerals free; positive-domain equivalence is proved separately",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
