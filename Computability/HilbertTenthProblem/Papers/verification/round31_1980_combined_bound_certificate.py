#!/usr/bin/env python3
"""Same 96-operation linear-radix certificate with 34 positive witnesses.

The positive witness maps are proved in COMBINED_BOUND_96_PROOF.md.
This verifies the complete primitive schedule and every source residual.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round30_1980_linear_radix_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round31_1980_combined_bound_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = [name for name in previous.NAMES if name != "al2"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS[:-1])
EQUATION_LABELS[0] = "combined_code_bound"
EQUALITIES = list(previous.EQUALITIES[:-1])
EQUALITIES[0] = ("L1", "q")


def make_schedule():
    result = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "indicator_bound":
            baseline.need((operation, left, right) == ("+", "l", "al2"),
                          "remove the separate indicator gap")
            continue
        if target == "L1":
            baseline.need((operation, left, right) == ("+", "S2", "al"),
                          "replace the packed-code gap")
            result.append(("bound_sum", "+", "l", "e"))
            left = "bound_sum"
        result.append((target, operation, left, right))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    result = previous.source_residuals()[:-1]
    s = SYM
    result[0] = s["l"]+s["e"]+s["al"]-s["q"]
    return result


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]
    D = A*A-1
    K_source, K_calculated = D*(s["f"]**2-1), env["ic22"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: -source[15]*(K_source+K_calculated-1)*H17**2,
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 equations and tests")
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
    old = previous.source_residuals()
    for index in range(1, len(source)):
        baseline.need(sp.expand(source[index]-old[index]) == 0,
                      "all source equations beyond the bound remain exact")
    old_alpha = s["l"]*(s["q"]-1)+s["al"]*s["q"]
    old_alpha2 = s["e"]+s["al"]
    baseline.need(sp.expand(old[0].subs(s["al"], old_alpha)-s["q"]*source[0]) == 0,
                  "old first residual restores as q times the new bound")
    baseline.need(sp.expand(old[-1].subs(previous.SYM["al2"], old_alpha2)-source[0]) == 0,
                  "old indicator residual restores as the new bound")
    for index in (3, 15):
        baseline.need(records[index]["triangular_correction_polynomial"] == "0",
                      "every correction has an independently exact prerequisite")
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 96 and counts == {"+": 44, "*": 52},
                  "unchanged96-operation count")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need("al2" not in env and "indicator_bound" not in env,
                  "discarded witness and gap register are absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 96,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 52},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": [0],
        "removed_source_index_zero_based": 22,
        "witness_map_checks": {
            "old_alpha": sp.sstr(old_alpha), "old_alpha2": sp.sstr(old_alpha2),
            "old_first_residual_equals_q_times_new_bound": True,
            "old_last_residual_equals_new_bound": True,
            "reverse_positive_gap": "q-ell-e; positivity follows from canonical code digits at most three",
        },
        "proofs": ["../1980/COMBINED_BOUND_96_PROOF.md",
                   "../1980/LINEAR_RADIX_96_PROOF.md"],
        "scope": "complete96-operation arithmetic certificate with34 positive witnesses; witness maps and universality proved separately; numerals and equality tests free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
