#!/usr/bin/env python3
"""113 instructions by shifting the first Pell parameter by one.

Let X=2*w*s^2*r^2*n^6, the value already computed by R8. Replace the
old parameter p=X by the mathematical parameter P=X+1, omit p and its
equality, evaluate P^2-1 as X*(X+2), and use h*X in E11. P itself is
never computed. The changed Pell ratio requires the independent proof
in ../1980/PELL_SHIFTED_BASE_PROOF.md; exact residual checks alone do
not establish positive-domain equivalence.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round5_1980_certificate as previous
from round4_1980_optimized_certificate import primitive_instructions, replace_block

HERE = Path(__file__).resolve().parent
OUT = HERE / "round5_1980_shifted_pell_certificate.json"
L = previous.L
PARAMETERS = list(previous.PARAMETERS)
NAMES = [name for name in previous.NAMES if name != "p"]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)
baseline.need(EQUATION_LABELS[7] == "E8" and EQUALITIES[7] == ("p", "R8"),
              "remove precisely the old defining equation for p")
del EQUATION_LABELS[7]
del EQUALITIES[7]


def make_schedule():
    schedule = list(previous.SCHEDULE)
    baseline.need(len(schedule) == 114, "114-operation predecessor")
    replace_block(schedule, ["p2", "p2m1"], [
        ("Xplus2", "+", "R8", 2),
        ("p2m1", "*", "R8", "Xplus2"),
    ])
    replace_block(schedule, ["pm1", "hpm1"], [("hpm1", "*", "h", "R8")])
    baseline.need(len(schedule) == 113, "113-operation shifted-Pell schedule")
    baseline.need(all("p" not in row for row in schedule), "p is no longer used")
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = list(previous.source_residuals())
    s = SYM
    X = 2*s["w"]*s["s"]**2*s["r"]**2*s["n"]**6
    # Write the source equations with their mathematical parameter P=X+1;
    # the certificate instead uses the factored coefficient X*(X+2).
    source[8] = ((X + 1)**2 - 1)*s["k"]**2 + 1 - s["tau"]**2
    source[11] = s["k"] - s["r"] - 1 - s["h"]*X
    del source[7]
    return source


def verify_certificate():
    baseline.need(len(NAMES) == len(set(NAMES)) == 36, "36 distinct positive inputs")
    baseline.need(set(PARAMETERS) <= set(NAMES), "four supplied parameters declared")
    baseline.need(len(set(NAMES) - set(PARAMETERS)) == 32, "32 positive witnesses")
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]*(s["n"]**2 - 1),
        16: source[15]*(s["a"] + 1)*(G_source + G_calculated)*H**2,
    }
    baseline.need(len(source) == len(EQUALITIES) == len(EQUATION_LABELS) == 20,
                  "20 explicitly enumerated equations")
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual - residual - correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual + residual) == 0:
            sign = -1
        else:
            raise AssertionError(f"residual mismatch at {EQUATION_LABELS[index]}")
        records.append({
            "equation": EQUATION_LABELS[index], "equality": [left, right],
            "source_residual_polynomial": sp.sstr(sp.expand(residual)),
            "certificate_residual_polynomial": sp.sstr(actual),
            "source_residual_sign": sign,
            "triangular_correction_polynomial": sp.sstr(sp.expand(correction)),
        })
    primitives = primitive_instructions(SCHEDULE)
    primitive_histogram = {"+": 0, "*": 0}
    for row in primitives:
        operation = row["operation"]
        baseline.need(operation in primitive_histogram, "addition/multiplication only")
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right, target = (value(row[name]) for name in ["left", "right", "result"])
        result = left + right if operation == "+" else left*right
        baseline.need(sp.expand(result - target) == 0, "serialized primitive identity")
        primitive_histogram[operation] += 1
    used = {name for _, _, left, right in SCHEDULE for name in (left, right)
            if isinstance(name, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "only declared source symbols; p eliminated")
    baseline.need(sum(histogram.values()) == len(primitives) == 113, "113 total operations")
    baseline.need(primitive_histogram == {"+": 50, "*": 63}, "final primitive histogram")
    X = 2*s["w"]*s["s"]**2*s["r"]**2*s["n"]**6
    baseline.need(sp.expand(env["R8"] - X) == 0, "shared parameter offset X")
    baseline.need(sp.expand(env["p2m1"] - ((X + 1)**2 - 1)) == 0,
                  "shifted Pell coefficient identity")
    constants = previous.verify_constants()
    return {
        "status": "PASS", "operations": 113, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 50, "multiplications": 63},
        "unknowns": 32, "equations": 20, "equality_tests": len(EQUALITIES),
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "auxiliary_domain": "integers, including signed of-d",
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records,
        "exponent_numeral": str(L), "coefficient_witnesses": previous.short.NU,
        "input_admissibility": {
            "normalization": "R=24*S+z*(sigma-1), S the zero-constant gated sum of squares",
            "digits": "R=sum c_i P_i monomials, P_0=-z, -z<P_i<z otherwise; Z=2z",
            "packed_index": "V=e_0(Z)+l_0(Z)*Z^L; L=5^64",
            "radix_scale": "H a power of two >max(2*Z^(2L+1),Z*62^4,3L,64)",
            "scope": "Z,V,H are fixed admissible encoding parameters, not existential witnesses",
        },
        "triangular_identities": [
            "F7calc=F7source+(lambda*F3-F2)*q*(n^2-1)",
            "F17calc=F17source+F16*(a+1)*(G_source+G_calculated)*(2r+1+jc)^2",
        ],
        "shifted_pell_parameter": {
            "offset": "X=2*w*s^2*r^2*n^6, already computed as R8",
            "mathematical_parameter": "P=X+1; neither an input nor an extra instruction",
            "coefficient": "P^2-1=X*(X+2)",
            "index_congruence": "k=r+1+h*X",
            "removed_unknown_and_equality": "p; E8:p=R8",
            "witness_map": "Rechoose k,tau,h,eta,zeta at Pell parameter X+1; preserve other witnesses",
        },
        "proofs": ["../1980/SHORT_MASKS_PROOF.md", "../1980/PELL_SIGNED_PROOF.md",
                   "../1980/PELL_PARITY_PROOF.md", "../1980/PELL_INTERVAL_PROOF.md",
                   "../1980/PELL_SHIFTED_BASE_PROOF.md"],
        "numerals_from_one": constants,
        "operations_with_numerals_from_one": 113 + constants["operations"],
        "scope": "short-mask indices, signed Pell congruence, linear ratio bounds, shifted first Pell base",
        "optimality_claimed": False,
    }


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", receipt["operations"], "operations", receipt["straight_line_histogram"],
          ";", receipt["equality_tests"], "equalities;", receipt["unknowns"], "positive witnesses")
    print("Every residual and primitive verified exactly;",
          receipt["operations_with_numerals_from_one"], "including fixed literal construction")
    print("wrote", OUT.name)
