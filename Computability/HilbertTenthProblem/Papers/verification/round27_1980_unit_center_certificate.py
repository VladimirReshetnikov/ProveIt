#!/usr/bin/env python3
"""98 operations: a unit-centered coefficient code with a direct guard.

The complete positive-domain argument and rebuilt admissible index are
in UNIT_CENTER_ENCODING_PROOF.md. Fixed numerals are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round26_1980_composed_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round27_1980_unit_center_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    result = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "twice_lambda":
            baseline.need((operation, left, right) == ("*", 2, "la"),
                          "the separate doubled coefficient disappears")
            continue
        if target == "three_lambda":
            baseline.need((operation, left, right) == ("+", "twice_lambda", "la"),
                          "three lambda is now a direct multiplication")
            operation, left, right = "*", 3, "la"
        elif target == "t2":
            baseline.need(left == "twice_lambda", "the new coefficient is lambda-e")
            left = "la"
        result.append((target, operation, left, right))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    q, n, C = s["q"], s["n"], s["x"]+s["g"]
    S3 = s["th"]*s["la"]*q - (s["la"]-s["e"])*C**2
    S2 = s["l"]+s["e"]*q
    S = s["g"]+q**2*(S2+q**2*S3)
    Tplus = q**2*(1+s["th"]*s["la"])-(s["b"]-1)*s["l"]+s["th"]*s["l"]*q**4
    source[6] = s["r"]-S*(n**2-n)-Tplus*(n**2-1)
    source[20] = S3-s["sigma"]
    source[21] = s["la"]-s["e"]-s["Omega"]
    return source


def verify_target_forms():
    x, u, v, y, w, delta = sp.symbols("x u v y w delta")
    coordinates = [x, delta, u, v, y, w]
    paired = {"product": u*v-w*delta, "sum": (u+v-w)*delta,
              "copy": (u-v)*delta, "zero": u*delta}
    rows = {f"{name}_{sign:+d}": sign*row
            for name, row in paired.items() for sign in (-1, 1)}
    rows.update({"unit_lower": u*delta-delta**2,
                 "unit_boolean_with_copy": u*delta-u*v})
    targets = {name: 2*row+delta**2 for name, row in rows.items()}
    targets["direct_guard"] = 2*y*delta-x**2+delta**2
    targets["first_special"] = delta**2
    records = []
    for name, expression in targets.items():
        target = sp.Poly(expression, *coordinates)
        coefficients = []
        for monomial, coefficient in target.terms():
            baseline.need(sum(monomial) == 2, "homogeneous quadratic target")
            multinomial = 1 if 2 in monomial else 2
            divided = coefficient/multinomial
            baseline.need(divided in {-1, 0, 1}, "unit-centered coefficient alphabet")
            coefficients.append(int(divided))
        records.append({"name": name, "target": sp.sstr(expression),
                        "D_coefficients": coefficients})
    for query in range(1, 65):
        guard_aux = (query*query+1)//2
        for carry in (-1, 0):
            baseline.need(not (0 <= -query*query+carry <= 3),
                          "the direct guard excludes delta zero independently of copies")
            raw = 2*guard_aux-query*query+1
            baseline.need(raw == 1+(query % 2), "positive guard necessity witness")
            baseline.need(0 <= raw+carry <= 3, "guard survives either incoming carry")
    for unit in range(20):
        for copied in range(20):
            copies_hold = unit-copied in (0, 1) and copied-unit in (0, 1)
            unit_rows_hold = unit-1 in (0, 1) and unit-unit*copied in (0, 1)
            baseline.need((copies_hold and unit_rows_hold) == (unit == copied == 1),
                          "paired copy and the two unit rows force one")
    return {"coefficient_alphabet": [-1, 0, 1], "canonical_digits": [0, 1, 2],
            "centering_digit": 1, "targets": records,
            "scope": "exact target polynomials and finite guard/unit regressions; the universal proof is separate"}


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    D = A*A-1
    K_source, K_calculated = D*(s["f"]**2-1), D*env["AE"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: source[15]*D*(K_source+K_calculated-1)*H17**2,
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
                          "all geometry and Pell source equations are unchanged")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 98 and primitive_histogram == {"+": 43, "*": 55},
                  "98-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need("twice_lambda" not in set(env) | used,
                  "the doubled coefficient register is absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 98, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 43, "multiplications": 55},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "normal_form_checks": verify_target_forms(),
        "support_checks": previous.ancestor.verify_dynamic_support(),
        "fixed_index": "V,H,Tindex=psi_4(L), rebuilt using unit-centered coefficients, copied unit Boolean coordinates, and the direct guard",
        "proofs": ["../1980/UNIT_CENTER_ENCODING_PROOF.md",
                   "../1980/COMPOSED_99_PROOF.md"],
        "scope": "exact 98-instruction arithmetic certificate with free fixed numerals; positive-domain equivalence and index construction are proved separately",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
