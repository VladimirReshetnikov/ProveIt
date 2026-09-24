#!/usr/bin/env python3
"""95-operation additive-radix certificate; fixed numerals are free.

This checks all primitive instructions and a fresh complete source list.
Universality and positive witnesses require AFFINE_RADIX_95_PROOF.md;
the separate encoding checker supplies only finite carry regressions.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round31_1980_combined_bound_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round32_1980_affine_radix_certificate.json"
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    result = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "bm1":
            baseline.need((operation, left, right) == ("-", "b", 1),
                          "delete the separate first-mask subtraction")
            continue
        if target == "B":
            baseline.need((operation, left, right) == ("*", "H", "b"),
                          "replace the radix product by the radix sum")
            operation = "+"
        elif target == "lbm1":
            baseline.need((operation, left, right) == ("*", "l", "bm1"),
                          "use b itself as the first-mask coefficient")
            right = "b"
        result.append((target, operation, left, right))
    return result


SCHEDULE = make_schedule()


def source_residuals():
    s = SYM
    x, a, b, c, d, e, f, g, h, i, j, k, ell, n, o, q, r, ss, t, w = (
        s[name] for name in
        ("x", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
         "k", "l", "n", "o", "q", "r", "s", "t", "w"))
    B, A, C = s["H"]+b, a+4, x+g
    D = A*A-1
    U, Y = w*n*n, ss*n*n
    la, th = s["la"], s["th"]
    sigma = (la-e)*(q-C*C)
    S = g+q*q*(ell+e*q+q*q*sigma)
    Tplus = q*q*(1+th*la)-b*ell+th*ell*q**4
    K = D*(f*f-1)
    v, J = o*f-d*d, 2*r+1
    return [
        ell+e+s["al"]-q,
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
    ]


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]+s["b"]
    D = A*A-1
    K_source, K_calculated = D*(s["f"]**2-1), env["ic22"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        2: -s["la"]*source[3],
        16: -source[15]*(K_source+K_calculated-1)*H17**2,
        17: source[3]*(s["ka"]+s["rho"]*(source[3]-2*(A-B))),
    }
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 equations and equality tests")
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
    old = previous.source_residuals()
    changed = {2, 3, 6, 17}
    for index, residual in enumerate(source):
        if index not in changed:
            baseline.need(sp.expand(residual-old[index]) == 0,
                          "all source equations outside the declared change are exact")
    baseline.need(sp.expand(source[6]-old[6]-s["l"]*(s["n"]**2-1)) == 0,
                  "the packed source changes by exactly ell*(n squared minus one)")
    for name, expression in {
        "B": B,
        "lbm1": s["l"]*s["b"],
        "S3": (s["la"]-s["e"])*(s["q"]-(s["x"]+s["g"])**2),
    }.items():
        baseline.need(sp.expand(env[name]-expression) == 0, "shared register: " + name)
    primitives, counts = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 95 and counts == {"+": 44, "*": 51},
                  "95-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need("bm1" not in env and "bm1" not in used, "removed subtraction register is absent")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 95,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 44, "multiplications": 51},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "changed_source_indices_zero_based": sorted(changed),
        "fixed_index": "H=H0+1 with H0 a sufficiently large power of two; V and Tindex=psi_4(L) rebuilt from the physical three-way code",
        "proofs": ["../1980/AFFINE_RADIX_95_PROOF.md", "../1980/COMBINED_BOUND_96_PROOF.md"],
        "scope": "complete95-operation arithmetic certificate; general encoding and positive-witness correctness require the separate proof; fixed numerals and equality tests free",
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["operations"], receipt["straight_line_histogram"])
    print(receipt["unknowns"], "positive unknowns;", receipt["equations"], "equalities")
