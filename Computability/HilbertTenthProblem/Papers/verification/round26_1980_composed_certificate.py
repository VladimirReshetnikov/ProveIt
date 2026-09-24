#!/usr/bin/env python3
"""99 operations: compose the half-center encoding and doubled Pell index.

The proof is COMPOSED_99_PROOF.md.  Fixed numerals are free.  This
standalone verifier checks the whole circuit and both transformation
orders, without treating proof equivalence as a symbolic consequence.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round23_1980_fixed_four_certificate as ancestor
import round24_1980_doubled_pell_certificate as pell
import round25_1980_half_center_certificate as coding
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round26_1980_composed_certificate.json"
PARAMETERS = list(pell.PARAMETERS)
NAMES = list(pell.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(pell.EQUATION_LABELS)
EQUALITIES = list(coding.EQUALITIES)
EQUALITIES[16] = pell.EQUALITIES[16]


def apply_pell(schedule):
    result = []
    for target, operation, left, right in schedule:
        if target in ("am1", "ap1", "R17"):
            continue
        if target == "A":
            baseline.need((operation, left, right) == ("*", "am1", "ap1"),
                          "replace the factored norm coefficient")
            result.extend([("a_square", "*", "a", "a"),
                           ("A", "+", "a_square", "a4m5")])
            continue
        if target == "dof":
            right = "L15"
        elif target == "L17":
            result.append(("vplus1", "+", "dof", 1))
            right = "vplus1"
        elif target == "Gminus1":
            left = "A"
        elif target == "Gplus1":
            operation, right = "-", 1
        elif target == "Dam1":
            right = "a"
        elif target == "R20":
            right = "Tindex"
        result.append((target, operation, left, right))
    return result


def apply_coding(schedule):
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
    result = []
    for instruction in schedule:
        if instruction[0] == "L2":
            result.extend(replacement)
        if instruction[0] not in removed_names:
            result.append(instruction)
    return result


SCHEDULE = apply_pell(coding.SCHEDULE)


def rename_index(residual):
    return residual.subs(ancestor.SYM["L"], SYM["Tindex"])


def source_residuals():
    source = [rename_index(residual) for residual in coding.source_residuals()]
    source[16] = pell.source_residuals()[16]
    source[19] = pell.source_residuals()[19]
    return source


def verify_certificate():
    baseline.need(apply_pell(ancestor.SCHEDULE) == pell.SCHEDULE,
                  "exact independent Pell transformation")
    baseline.need(apply_coding(ancestor.SCHEDULE) == coding.SCHEDULE,
                  "exact independent coding transformation")
    baseline.need(SCHEDULE == apply_coding(pell.SCHEDULE), "the full schedules commute")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    D = A*A-1
    K_source = D*(s["f"]**2-1)
    K_calculated = D*env["AE"]
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
    # E4 has an exact residual and is checked before E3 in the proof order.
    baseline.need(records[3]["triangular_correction_polynomial"] == "0",
                  "geometric correction depends only on an independently exact equality")
    old = ancestor.source_residuals()
    pell_source, coding_source = pell.source_residuals(), coding.source_residuals()
    for index, residual in enumerate(source):
        pell_delta = pell_source[index]-rename_index(old[index])
        coding_delta = rename_index(coding_source[index]-old[index])
        baseline.need(sp.expand(residual-rename_index(coding_source[index])-pell_delta) == 0,
                      "coding then Pell source composition")
        baseline.need(sp.expand(residual-pell_source[index]-coding_delta) == 0,
                      "Pell then coding source composition")
        if index not in (6, 16, 19, 20, 21):
            baseline.need(sp.expand(residual-rename_index(old[index])) == 0,
                          "all other source equations are unchanged")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 99 and primitive_histogram == {"+": 44, "*": 55},
                  "99-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    baseline.need(not ({"am1", "ap1", "Lam", "zl", "twice_e", "L"} & (set(env) | used)),
                  "the unused registers of both transformations are absent")
    return {
        "status": "PASS", "operations": 99, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 55},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "normal_form_checks": coding.verify_target_forms(),
        "support_checks": ancestor.verify_dynamic_support(),
        "composition_checks": {"schedules_commute": True, "all_source_residuals_commute": True,
                               "changed_source_indices_zero_based": [6, 16, 19, 20, 21],
                               "equality_proof_order": "E4 before E3; E16 before E17; E4 before E18"},
        "fixed_index": "V,H,Tindex=psi_4(L), using the half-center paired circuit index at the underlying power-of-two exponent L",
        "proofs": ["../1980/COMPOSED_99_PROOF.md", "../1980/HALF_CENTER_ENCODING_PROOF.md",
                   "../1980/PELL_DOUBLED_INDEX_PROOF.md", "../1980/PELL_COMMON_WITNESS_PROOF.md"],
        "scope": "exact 99-instruction arithmetic certificate with both composition orders checked; fixed numerals free; positive-domain equivalence proved separately",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
