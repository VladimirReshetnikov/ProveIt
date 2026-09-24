#!/usr/bin/env python3
"""101 operations with a unit-coefficient circuit encoding and fixed Z=4.

The three set-dependent parameters are now V,H,L.  L is a sufficiently
large power of two chosen after compiling the represented polynomial to
primitive circuit rows.  The proof is FIXED_FOUR_ENCODING_PROOF.md.
All numerals and supplied index parameters are free.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round22_1980_composed_certificate as previous
from round13_1980_certificate import verify_primitives

HERE = Path(__file__).resolve().parent
OUT = HERE / "round23_1980_fixed_four_certificate.json"
PARAMETERS = ["x", "V", "H", "L"]
NAMES = ["L" if name == "Z" else name for name in previous.NAMES]
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUATION_LABELS = list(previous.EQUATION_LABELS)
EQUALITIES = list(previous.EQUALITIES)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "b5m2":
            baseline.need((operation, left, right) == ("-", "B", 4),
                          "theta is already B-4")
            continue
        left = 4 if left == "Z" else "th" if left == "b5m2" else left
        right = 4 if right == "Z" else "th" if right == "b5m2" else right
        if target == "R20":
            baseline.need(right == previous.L, "replace only the fixed exponent index")
            right = "L"
        schedule.append((target, operation, left, right))
    return schedule


SCHEDULE = make_schedule()


def source_residuals():
    source = [residual.subs(previous.SYM["Z"], 4)
              for residual in previous.source_residuals()]
    source[19] += previous.L - SYM["L"]
    return source


def verify_normal_forms():
    x, u, v, y, z, delta = sp.symbols("x u v y z delta")
    coordinates = [x, delta, u, v, y, z]
    rows = {
        "product_of_distinct_coordinates": u*v-z*delta,
        "sum_of_distinct_coordinates": (u+v-z)*delta,
        "copy_or_output_equality": (u-v)*delta,
        "unit": (u-delta)*delta,
        "zero": u*delta,
        "guard": y*delta-x*x,
    }
    records = []
    for name, residual in rows.items():
        target = sp.Poly(2*residual + delta*delta, *coordinates)
        coefficients = []
        for monomial, coefficient in target.terms():
            baseline.need(sum(monomial) == 2, "homogeneous quadratic target")
            multinomial = 1 if 2 in monomial else 2
            encoded = coefficient / multinomial
            baseline.need(encoded in {-2, -1, 0, 1}, "fixed-four coefficient alphabet")
            coefficients.append(int(encoded))
        records.append({"row": name, "residual": sp.sstr(residual),
                        "D_coefficients": coefficients})
    for residual in range(-20, 21):
        for carry in (-1, 0):
            baseline.need((0 <= 4*residual + 2 + carry <= 3) == (residual == 0),
                          "borrow-tolerant ordinary target")
    for unit in range(20):
        for carry in (-1, 0):
            if 0 <= 2*unit*unit + carry <= 3:
                baseline.need(unit in (0, 1), "special target recovers zero or one")
    return {"coefficient_alphabet": [-2, -1, 0, 1], "centering_digit": 2,
            "canonical_digit_alphabet": [0, 1, 2, 3], "rows": records,
            "scope": "exact normal-form identities and finite carry regressions; universal compilation and carry proof are in the companion proof"}


def verify_dynamic_support():
    samples = []
    for count in (2, 3, 6, 12, 24):
        weights = [0] + [3**index for index in range(count)]
        pair_sums = [weights[i] + weights[j]
                     for i in range(len(weights)) for j in range(i, len(weights))]
        baseline.need(len(pair_sums) == len(set(pair_sums)), "base-three Sidon support")
        maximum = weights[-1]
        for rows in (2, 3, 8, 32):
            spacing = 4*maximum + 1
            first = (rows+1)*spacing + 2*maximum
            last = first + (rows-1)*spacing
            K = last + 1
            exponent = 1 << (3*K+2).bit_length()
            baseline.need(first-2*maximum > maximum, "low variable region is clear")
            baseline.need(2*first-2*maximum > last, "dummy coordinates miss targets")
            baseline.need(spacing > 4*maximum, "different target rows do not interact")
            baseline.need(exponent > 3*K+2, "power-of-two exponent has all degree margins")
            samples.append({"positive_weight_coordinates": count, "rows": rows,
                            "K": K, "L": exponent})
    return {"variable_weights": "0 for x; 3^i for the other low coordinates, with delta at i=0",
            "row_spacing": "d=4*vmax+1",
            "target_weights": "(t+1)*d+2*vmax+j*d, 0<=j<t",
            "exponent": "set-dependent power of two L>3*(last_target+1)+2",
            "scope": "finite exact support regressions; the base-three uniqueness and general inequalities are proved in the companion proof",
            "samples": samples}


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source, s = source_residuals(), SYM
    A, B = s["a"]+4, s["H"]*s["b"]**2
    G_source = 1 + (A+1)*(s["f"]**2-1)
    G_calculated = 1 + (A+1)*env["AE"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        6: ((s["la"]*source[3]-source[2])*s["q"]**2
            - source[3]*s["l"]*s["q"]**4)*(s["n"]**2-1),
        16: source[15]*(A+1)*(G_source+G_calculated)*H17**2,
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
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 101 and primitive_histogram == {"+": 45, "*": 56},
                  "101-operation histogram")
    used = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
            if isinstance(operand, str)} | {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "all positive inputs participate")
    baseline.need(len(NAMES) == 38 and len(PARAMETERS) == 4, "34 positive unknowns")
    baseline.need(not ({"Z", "b5m2"} & (set(env) | used)), "fixed-four register sharing")
    baseline.need(set().union(*(res.free_symbols for res in source)) <= set(SYM.values()),
                  "all source symbols are declared")
    return {
        "status": "PASS", "operations": 101, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 45, "multiplications": 56},
        "unknowns": 34, "equations": 22, "equality_tests": 22,
        "parameters": PARAMETERS, "positive_input_names": NAMES,
        "positive_unknown_names": [name for name in NAMES if name not in PARAMETERS],
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "normal_form_checks": verify_normal_forms(),
        "support_checks": verify_dynamic_support(),
        "proofs": ["../1980/FIXED_FOUR_ENCODING_PROOF.md",
                   "../1980/COMPOSED_102_PROOF.md", "../1980/PELL_COMMON_WITNESS_PROOF.md"],
        "fixed_index": "V,H,L; Z=4 is universal; L is a set-dependent power of two",
        "scope": "exact 101-instruction arithmetic certificate; fixed numerals free; positive-domain equivalence and dynamic coefficient compilation are proved separately",
    }


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], result["operations"], result["straight_line_histogram"])
    print(result["unknowns"], "positive unknowns;", result["equations"], "equalities")
