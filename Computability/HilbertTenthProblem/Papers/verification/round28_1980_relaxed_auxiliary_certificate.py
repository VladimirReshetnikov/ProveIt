#!/usr/bin/env python3
"""98 operations: a relaxed auxiliary Pell norm with recovered integrality.

Replace E16 by (i*c^2)^2=D*(f^2-1), D=(a+4)^2-1.
The existing square is then the K register in the doubled signed norm.
The proof is PELL_RELAXED_AUXILIARY_PROOF.md; fixed numerals are free.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

import round4_1980_operation_count as baseline
import round26_1980_composed_certificate as previous
import round25_1980_half_center_certificate as coding
import round23_1980_fixed_four_certificate as fixed_four
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round28_1980_relaxed_auxiliary_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
EQUALITIES[15] = ("ic22", "R16")


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target in ("AE", "R16", "Gminus1"):
            continue
        left = "ic22" if left == "Gminus1" else left
        right = "ic22" if right == "Gminus1" else right
        schedule.append((target, operation, left, right))
        if target == "L16":
            schedule.extend([("f_square_minus_one", "-", "L16", 1),
                             ("R16", "*", "A", "f_square_minus_one")])
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    D = (s["a"]+4)**2-1
    source[15] = (s["i"]*s["c"]**2)**2-D*(s["f"]**2-1)
    return source


def verify_certificate():
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
    for index, old_residual in enumerate(previous.source_residuals()):
        if index != 15:
            baseline.need(sp.expand(source[index]-old_residual) == 0,
                          "only the auxiliary norm source equation changes")
    for name, value in {
        "ic22": (s["i"]*s["c"]**2)**2,
        "R16": K_source,
        "Gplus1": K_calculated-1,
    }.items():
        baseline.need(sp.expand(env[name]-value) == 0, "shared register: " + name)
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 98 and primitive_histogram == {"+": 44, "*": 54},
                  "98-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need(not ({"AE", "Gminus1"} & (set(env) | used)),
                  "the two old auxiliary products are absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 98,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 54},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "normal_form_checks": coding.verify_target_forms(),
        "support_checks": fixed_four.verify_dynamic_support(),
        "changed_equation": "E16: (i*c^2)^2=((a+4)^2-1)*(f^2-1)",
        "shared_register": "K=(i*c^2)^2 is used directly in the doubled signed norm",
        "necessity_reparameterization": "new_i=D*old_i for the standard even-index auxiliary witnesses; all other witnesses can be retained",
        "fixed_index": "V,H,Tindex=psi_4(L), using the unchanged half-center index",
        "proofs": ["../1980/PELL_RELAXED_AUXILIARY_PROOF.md",
                   "../1980/COMPOSED_99_PROOF.md",
                   "../1980/PELL_DOUBLED_INDEX_PROOF.md"],
        "scope": "exact 98-instruction arithmetic certificate; Pell integrality, index divisibility, and positive-domain equivalence proved independently; fixed numerals free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
