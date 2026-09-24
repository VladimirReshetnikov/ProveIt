#!/usr/bin/env python3
"""100 operations: doubled-index signed Pell norm and a fixed Pell index.

The admissible index is (V,H,Tindex), where Tindex=psi_4(L) and V,H
are constructed from the underlying exponent L as in round23.
Positive-domain equivalence is proved in PELL_DOUBLED_INDEX_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

import round4_1980_operation_count as baseline
import round23_1980_fixed_four_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round24_1980_doubled_pell_certificate.json"
PARAMETERS = ["x", "V", "H", "Tindex"]
NAMES = ["Tindex" if name == "L" else name for name in previous.NAMES]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
EQUALITIES[16] = ("L17", "P17")


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target in ("am1", "ap1", "R17"):
            continue
        if target == "A":
            schedule.extend([("a_square", "*", "a", "a"),
                             ("A", "+", "a_square", "a4m5")])
            continue
        if target == "dof":
            right = "L15"
        elif target == "L17":
            schedule.append(("vplus1", "+", "dof", 1))
            right = "vplus1"
        elif target == "Gminus1":
            left = "A"
        elif target == "Gplus1":
            operation, right = "-", 1
        elif target == "Dam1":
            right = "a"
        elif target == "R20":
            right = "Tindex"
        schedule.append((target, operation, left, right))
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = [r.subs(previous.SYM["L"], SYM["Tindex"])
              for r in previous.source_residuals()]
    s = SYM
    D = (s["a"]+4)**2-1
    v = s["o"]*s["f"]-s["d"]**2
    K = D*(s["f"]**2-1)
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    source[16] = v*(v+1)-K*(K-1)*H17**2
    source[19] = s["ka"]-s["Tindex"]-s["Delta"]*s["a"]
    return source


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    D = A*A-1
    K_source = D*(s["f"]**2-1)
    K_calculated = D*env["AE"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        6: ((s["la"]*source[3]-source[2])*s["q"]**2
            - source[3]*s["l"]*s["q"]**4)*(s["n"]**2-1),
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
    for name, expression in {
        "A": D,
        "dof": s["o"]*s["f"]-s["d"]**2,
        "Gminus1": K_calculated,
        "Gplus1": K_calculated-1,
        "Dam1": s["Delta"]*s["a"],
    }.items():
        baseline.need(sp.expand(env[name]-expression) == 0, "register meaning: " + name)
    old_source = [r.subs(previous.SYM["L"], s["Tindex"])
                  for r in previous.source_residuals()]
    for index in range(22):
        if index not in (16, 19):
            baseline.need(sp.expand(source[index]-old_source[index]) == 0,
                          "only E17 and E20 change after renaming the fixed index")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 100 and primitive_histogram == {"+": 44, "*": 56},
                  "100-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need(not ({"am1", "ap1", "R17", "L"} & (set(env) | used)),
                  "unused affine parameters and the old fixed-index input are absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 100,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 56},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "normal_form_checks": previous.verify_normal_forms(),
        "support_checks": previous.verify_dynamic_support(),
        "fixed_index": "V,H,Tindex with Tindex=psi_4(L), using the round23 index construction at the underlying power-of-two exponent L",
        "register_meanings": {
            "A": "D=(a+4)^2-1=a^2+(8a+15)",
            "dof": "v=o*f-d^2, an integer register which may be signed",
            "Gminus1": "K=D*(f^2-1), using E16",
            "Gplus1": "K-1; the mathematical auxiliary Pell base is G=2K-1",
        },
        "proofs": ["../1980/PELL_DOUBLED_INDEX_PROOF.md",
                   "../1980/FIXED_FOUR_ENCODING_PROOF.md",
                   "../1980/PELL_COMMON_WITNESS_PROOF.md"],
        "scope": "exact 100-instruction arithmetic certificate; positive-domain equivalence and fixed-index replacement proved independently; fixed numerals free",
    }


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], result["operations"], result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", result["equations"], "equalities")
