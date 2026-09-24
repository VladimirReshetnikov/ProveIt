#!/usr/bin/env python3
"""93 operations for the unchanged shifted-affine system, by factoring ell.

The complete mathematical system and admissible fixed indices are those of
SHIFTED_AFFINE_94_PROOF.md. FACTORED_MASK_93_PROOF.md proves the schedule
identity and unchanged positive-witness equivalence. Fixed numerals are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round33_1980_shifted_affine_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round34_1980_factored_mask_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
OLD_BLOCK = [
    ("Tq4", "*", "Tcoef", "q2"),
    ("lbm1", "*", "l", "b"),
    ("T2", "-", "Tq4", "lbm1"),
    ("packed_target_shift", "*", "l", "q4"),
    ("mask_term", "*", "th", "packed_target_shift"),
    ("T", "+", "T2", "mask_term"),
]
NEW_BLOCK = [
    ("Tq4", "*", "Tcoef", "q2"),
    ("theta_q4", "*", "th", "q4"),
    ("mask_gap", "-", "theta_q4", "b"),
    ("indicator_mask", "*", "l", "mask_gap"),
    ("T", "+", "Tq4", "indicator_mask"),
]


def make_schedule():
    start = previous.SCHEDULE.index(OLD_BLOCK[0])
    baseline.need(previous.SCHEDULE[start:start+len(OLD_BLOCK)] == OLD_BLOCK,
                  "the exact six-instruction mask block is replaced")
    removed = {row[0] for row in OLD_BLOCK} - {row[0] for row in NEW_BLOCK}
    outside = previous.SCHEDULE[:start] + previous.SCHEDULE[start+len(OLD_BLOCK):]
    used = {operand for _, _, left, right in outside for operand in (left, right)}
    used.update(name for pair in EQUALITIES for name in pair)
    baseline.need(not (removed & used), "deleted registers have no outside uses")
    return previous.SCHEDULE[:start] + NEW_BLOCK + previous.SCHEDULE[start+len(OLD_BLOCK):]


SCHEDULE = make_schedule()


def source_residuals():
    return previous.source_residuals()


def verify_certificate():
    env, old_env = dict(SYM), dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    baseline.run_schedule(previous.SCHEDULE, old_env)
    for name in env.keys() & old_env.keys():
        baseline.need(sp.expand(env[name]-old_env[name]) == 0,
                      "every retained register has exactly its old value: " + name)
    baseline.need(sp.expand(env["T"]-old_env["T"]) == 0,
                  "the entire packed mask is unchanged without any source assumptions")
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
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 93 and counts == {"+": 43, "*": 50},
                  "93-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4,
                  "34 positive unknowns and four inputs")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    numerals = sorted({operand for row in primitives for operand in (row["left"], row["right"])
                       if isinstance(operand, int)})
    baseline.need(numerals == [1, 3, 8, 15], "the literal numerals are unchanged")
    return {
        "status": "PASS", "operations": 93,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 43, "multiplications": 50},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": [], "literal_numerals": numerals,
        "schedule_identity": "q^2*Tcoef-l*b+th*l*q^4 = q^2*Tcoef+l*(th*q^4-b)",
        "fixed_index": "Exactly the shifted-affine94 index; H=H0-3, V and Tindex unchanged",
        "positive_witness_map": "Identity on all 34 positive unknowns and all four inputs",
        "proofs": ["../1980/FACTORED_MASK_93_PROOF.md", "../1980/SHIFTED_AFFINE_94_PROOF.md"],
        "scope": "complete 93-operation certificate for the unchanged universal system; fixed numerals and equality tests free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
