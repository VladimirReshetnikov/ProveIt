#!/usr/bin/env python3
"""92 operations using the square root of the auxiliary doubled Pell base.

HALF_PARAMETER_PELL_92_PROOF.md proves both positive-domain directions.
The fixed index and coefficient encoding are unchanged from affine94.
Fixed numerals and equality tests are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round34_1980_factored_mask_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round35_1980_half_parameter_pell_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES) + ["y_aux"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS) + ["E17 normalized-root congruence"]
EQUALITIES = list(previous.EQUALITIES) + [("H17", "aux_u_rhs")]
OLD_BLOCK = [
    ("of", "*", "o", "f"),
    ("dof", "-", "of", "L15"),
    ("vplus1", "+", "dof", 1),
    ("L17", "*", "dof", "vplus1"),
    ("Gplus1", "-", "ic22", 1),
    ("G2m1", "*", "ic22", "Gplus1"),
    ("jc", "*", "j", "c"),
    ("H17", "+", "tr1", "jc"),
    ("H2", "*", "H17", "H17"),
    ("P17", "*", "G2m1", "H2"),
]
NEW_BLOCK = [
    ("of", "*", "o", "f"),
    ("aux_u_rhs", "+", "c", "of"),
    ("jc", "*", "j", "c"),
    ("H17", "+", "tr1", "jc"),
    ("H2", "*", "H17", "H17"),
    ("aux_y2", "*", "y_aux", "y_aux"),
    ("aux_square_gap", "-", "H2", "aux_y2"),
    ("L17", "*", "ic22", "aux_square_gap"),
    ("P17", "-", 1, "aux_y2"),
]


def make_schedule():
    start = previous.SCHEDULE.index(OLD_BLOCK[0])
    baseline.need(previous.SCHEDULE[start:start+len(OLD_BLOCK)] == OLD_BLOCK,
                  "replace exactly the ten-instruction signed auxiliary block")
    removed = {row[0] for row in OLD_BLOCK} - {row[0] for row in NEW_BLOCK}
    outside = previous.SCHEDULE[:start] + previous.SCHEDULE[start+len(OLD_BLOCK):]
    used = {operand for _, _, left, right in outside for operand in (left, right)}
    used.update(name for pair in EQUALITIES for name in pair)
    baseline.need(not (removed & used), "deleted temporaries have no outside uses")
    return previous.SCHEDULE[:start] + NEW_BLOCK + previous.SCHEDULE[start+len(OLD_BLOCK):]


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    D = (s["a"]+4)**2-1
    K_source = D*(s["f"]**2-1)
    u = 2*s["r"]+1+s["j"]*s["c"]
    source[16] = K_source*(u*u-s["y_aux"]**2)-(1-s["y_aux"]**2)
    source.append(u-s["c"]-s["o"]*s["f"])
    return source


def verify_certificate():
    env, old_env = dict(SYM), dict(previous.SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    baseline.run_schedule(previous.SCHEDULE, old_env)
    for name in (env.keys() & old_env.keys()) - {"L17", "P17"}:
        baseline.need(sp.expand(env[name]-old_env[name]) == 0,
                      "every retained non-auxiliary-output register is unchanged: " + name)
    source, s = source_residuals(), SYM
    A, B_math = s["a"]+4, s["H"]+s["b"]+4
    u = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: source[15]*(u*u-s["y_aux"]**2),
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B_math))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 23,
                  "23 complete source equations and equality tests")
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
    changed = [i for i, old in enumerate(previous.source_residuals())
               if sp.expand(old-source[i]) != 0]
    baseline.need(changed == [16], "only the old signed auxiliary source equation is replaced")
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 92 and counts == {"+": 43, "*": 49},
                  "92-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 39 and len(PARAMETERS) == 4,
                  "35 positive unknowns and four inputs")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "every source symbol is declared")
    numerals = sorted({operand for row in primitives for operand in (row["left"], row["right"])
                       if isinstance(operand, int)})
    baseline.need(numerals == [1, 3, 8, 15], "the literal numerals are unchanged")
    return {
        "status": "PASS", "operations": 92,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 43, "multiplications": 49},
        "unknowns": 35, "equations": 23, "equality_tests": 23,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": changed,
        "new_source_index_zero_based": 22, "literal_numerals": numerals,
        "fixed_index": "The affine94 translated index and coefficient encoding are unchanged",
        "auxiliary_equations": ["K*(u^2-y_aux^2)=1-y_aux^2", "u=c+o*f", "u=2*r+1+j*c", "K=D*(f^2-1)=(i*c^2)^2"],
        "proofs": ["../1980/HALF_PARAMETER_PELL_92_PROOF.md", "../1980/FACTORED_MASK_93_PROOF.md"],
        "scope": "complete 92-operation arithmetic certificate; positive-domain equivalence requires the separate half-parameter Pell proof; fixed numerals and equality tests free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
