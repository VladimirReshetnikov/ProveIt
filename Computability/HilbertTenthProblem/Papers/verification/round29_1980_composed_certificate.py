#!/usr/bin/env python3
"""97 operations: compose the unit-centered code and relaxed auxiliary norm.

COMPOSED_97_PROOF.md proves the positive-domain composition. This
standalone checker verifies both transformation orders, every primitive,
and all source residuals. Fixed numerals are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round26_1980_composed_certificate as ancestor
import round27_1980_unit_center_certificate as coding
import round28_1980_relaxed_auxiliary_certificate as pell
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round29_1980_composed_certificate.json"
PARAMETERS = list(ancestor.PARAMETERS)
NAMES = list(ancestor.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(ancestor.EQUATION_LABELS)
EQUALITIES = list(pell.EQUALITIES)


def apply_coding(schedule):
    result = []
    for target, operation, left, right in schedule:
        if target == "twice_lambda":
            baseline.need((operation, left, right) == ("*", 2, "la"),
                          "remove the separate doubled coefficient")
            continue
        if target == "three_lambda":
            baseline.need((operation, left, right) == ("+", "twice_lambda", "la"),
                          "replace the old three-lambda sum")
            operation, left, right = "*", 3, "la"
        elif target == "t2":
            baseline.need(left == "twice_lambda", "unit-centered coefficient")
            left = "la"
        result.append((target, operation, left, right))
    return result


def apply_pell(schedule):
    result = []
    for target, operation, left, right in schedule:
        if target in ("AE", "R16", "Gminus1"):
            continue
        left = "ic22" if left == "Gminus1" else left
        right = "ic22" if right == "Gminus1" else right
        result.append((target, operation, left, right))
        if target == "L16":
            result.extend([("f_square_minus_one", "-", "L16", 1),
                           ("R16", "*", "A", "f_square_minus_one")])
    return result


SCHEDULE = apply_pell(coding.SCHEDULE)


def source_residuals():
    source = list(coding.source_residuals())
    source[15] = pell.source_residuals()[15]
    return source


def verify_certificate():
    baseline.need(apply_coding(ancestor.SCHEDULE) == coding.SCHEDULE,
                  "the independent coding transformation agrees exactly")
    baseline.need(apply_pell(ancestor.SCHEDULE) == pell.SCHEDULE,
                  "the independent Pell transformation agrees exactly")
    baseline.need(SCHEDULE == apply_coding(pell.SCHEDULE),
                  "both orders give the same complete schedule")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    D = A*A-1
    K_source = D*(s["f"]**2-1)
    K_calculated = env["ic22"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: -source[15]*(K_source+K_calculated-1)*H17**2,
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 source equations and tests")
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
    old = ancestor.source_residuals()
    code_source, pell_source = coding.source_residuals(), pell.source_residuals()
    for index, residual in enumerate(source):
        code_delta = sp.expand(code_source[index]-old[index])
        pell_delta = sp.expand(pell_source[index]-old[index])
        baseline.need(sp.expand(residual-code_source[index]-pell_delta) == 0,
                      "coding then Pell source composition")
        baseline.need(sp.expand(residual-pell_source[index]-code_delta) == 0,
                      "Pell then coding source composition")
        baseline.need(code_delta == 0 or pell_delta == 0,
                      "the source transformations have disjoint support")
        if index not in (6, 15, 20, 21):
            baseline.need(sp.expand(residual-old[index]) == 0,
                          "all other source equations are unchanged")
    for index in (3, 15):
        baseline.need(records[index]["triangular_correction_polynomial"] == "0",
                      "every correction depends on an independently exact equation")
    for name, value in {"ic22": (s["i"]*s["c"]**2)**2,
                        "R16": K_source,
                        "t2": s["la"]-s["e"]}.items():
        baseline.need(sp.expand(env[name]-value) == 0, "shared register: " + name)
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 97 and primitive_histogram == {"+": 43, "*": 54},
                  "97-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need(not ({"twice_lambda", "AE", "Gminus1"} & (set(env) | used)),
                  "the removed registers of both transformations are absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 97,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 43, "multiplications": 54},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "normal_form_checks": coding.verify_target_forms(),
        "support_checks": coding.previous.ancestor.verify_dynamic_support(),
        "composition_checks": {"schedules_commute": True, "all_source_residuals_commute": True,
                               "changed_source_indices_zero_based": [6, 15, 20, 21],
                               "equality_proof_order": "E4 before E3; E16 before E17; E4 before E18"},
        "fixed_index": "V,H,Tindex=psi_4(L), rebuilt using the complete unit-centered code and direct guard",
        "necessity_reparameterization": "after the unit-centered coding and doubled-index witnesses are constructed, replace i by D*i; every other witness is retained",
        "proofs": ["../1980/COMPOSED_97_PROOF.md", "../1980/UNIT_CENTER_ENCODING_PROOF.md",
                   "../1980/PELL_RELAXED_AUXILIARY_PROOF.md", "../1980/COMPOSED_99_PROOF.md"],
        "scope": "exact 97-instruction arithmetic certificate and both transformation orders; fixed numerals free; positive-domain composition proved separately and independently reviewed",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
