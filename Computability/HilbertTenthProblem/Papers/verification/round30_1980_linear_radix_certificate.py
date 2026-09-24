#!/usr/bin/env python3
"""96-operation linear-radix certificate; fixed numerals are free.

The arithmetic verification is independent of the positive-domain proof
in LINEAR_RADIX_96_PROOF.md. The companion encoding checker verifies
finite support/carry regressions, not the general mathematical theorem.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

import round4_1980_operation_count as baseline
import round29_1980_composed_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round30_1980_linear_radix_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES) + ["al2"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS) + ["short_indicator_bound"]
EQUALITIES = list(previous.EQUALITIES) + [("indicator_bound", "q")]


def make_schedule():
    result = []
    for target, operation, left, right in previous.SCHEDULE:
        if target in ("b2", "P2"):
            continue
        if target == "B":
            baseline.need((operation, left, right) == ("*", "H", "b2"),
                          "replace the quadratic radix by H*b")
            right = "b"
        elif target == "P1":
            baseline.need((operation, left, right) == ("*", "t2", "C2"),
                          "replace the old coefficient product")
            target, operation, left, right = "code_gap", "-", "q", "C2"
        elif target == "S3":
            baseline.need((operation, left, right) == ("-", "P2", "P1"),
                          "factor the new third-block expression")
            operation, left, right = "*", "t2", "code_gap"
        result.append((target, operation, left, right))
        if target == "S2":
            result.append(("indicator_bound", "+", "l", "al2"))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    x, a, b, c, d, e, f, g, h, i, j, k, ell, n, o, q, r, ss, t, w = (
        s[name] for name in
        ("x", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
         "k", "l", "n", "o", "q", "r", "s", "t", "w"))
    B, A, C = s["H"]*b, a+4, x+g
    D = A*A-1
    U, Y = w*n*n, ss*n*n
    la, th = s["la"], s["th"]
    sigma = (la-e)*(q-C*C)
    S = g+q*q*(ell+e*q+q*q*sigma)
    Tplus = q*q*(1+th*la)-(b-1)*ell+th*ell*q**4
    K = D*(f*f-1)
    v = o*f-d*d
    J = 2*r+1
    return [
        ell+e*q+s["al"]-q*q,
        b-x-s["beta"],
        q*q-1-la*(B-1),
        th+4-B,
        ell+e*q-s["V"]-t*th,
        n-q**8,
        r-S*(n*n-n)-Tplus*(n*n-1),
        U*Y*Y*(U*Y*Y+1)*k*k-s["tau"]*(s["tau"]+1),
        c-Y*k-s["eta"],
        k-s["eta"]-s["zeta"],
        k-r-1-h*U*Y,
        a-Y*(U+1),
        c-s["ka"]-s["phi"],
        d-U-a*c-s["ga"]*(8*a+15),
        d*d-D*c*c-1,
        (i*c*c)**2-D*(f*f-1),
        v*(v+1)-K*(K-1)*(J+j*c)**2,
        s["mu"]-q-s["ka"]*(A-B)-s["rho"]*(D-(A-B)**2),
        D*s["ka"]**2+1-s["mu"]**2,
        s["ka"]-s["Tindex"]-s["Delta"]*a,
        sigma-s["sigma"],
        la-e-s["Omega"],
        ell+s["al2"]-q,
    ]


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
    baseline.need(len(source) == len(EQUALITIES) == 23, "23 equations and equality tests")
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
                      "every residual correction has an independently exact prerequisite")
    unchanged = set(range(22)) - {2, 3, 6, 17, 20}
    for index in unchanged:
        baseline.need(sp.expand(source[index]-previous.source_residuals()[index]) == 0,
                      "the retained source equation is unchanged")
    for name, expression in {
        "B": s["H"]*s["b"],
        "code_gap": s["q"]-(s["x"]+s["g"])**2,
        "S3": (s["la"]-s["e"])*(s["q"]-(s["x"]+s["g"])**2),
        "indicator_bound": s["l"]+s["al2"],
    }.items():
        baseline.need(sp.expand(env[name]-expression) == 0, "shared register: " + name)
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 96 and primitive_histogram == {"+": 44, "*": 52},
                  "96-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 39 and len(PARAMETERS) == 4, "35 positive unknowns")
    baseline.need(not ({"b2", "P1", "P2"} & (set(env) | used)),
                  "the three removed registers are absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 96,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 52},
        "unknowns": 35, "equations": 23, "equality_tests": 23,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": [2, 3, 6, 17, 20],
        "appended_source_index_zero_based": 22,
        "fixed_index": "V,H,Tindex=psi_4(L), rebuilt from paired zero targets and carry-reset padding",
        "proofs": ["../1980/LINEAR_RADIX_96_PROOF.md", "../1980/COMPOSED_97_PROOF.md"],
        "scope": "exact 96-instruction arithmetic certificate; positive-domain equivalence requires the separate linear-radix proof; fixed numerals free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
