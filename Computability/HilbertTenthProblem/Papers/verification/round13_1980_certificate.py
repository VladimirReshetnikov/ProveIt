#!/usr/bin/env python3
"""107 core operations, or 113 with all literal numerals generated from 1.

Use a modular Sidon layout with L=2**32. Move the existing a-1 register
before E14 and compute 4*a-5 as 4*(a-1)-1, eliminating literal 5 without
changing the core count. The encoding proof is MODULAR_SIDON_PROOF.md.
Every predecessor and its fixed indices remain unchanged.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline
import round12_1980_certificate as previous
from round4_1980_optimized_certificate import primitive_instructions

HERE = Path(__file__).resolve().parent
OUT = HERE / "round13_1980_certificate.json"
L = 2**32
PRIME = 61
PLACE_MULTIPLIER = 2*PRIME
ROWS = 1832
VARIABLE_WEIGHTS = tuple(1 + 3*(PLACE_MULTIPLIER*i + i*i % PRIME)
                         for i in range(60))
VMAX = max(VARIABLE_WEIGHTS)
ROW_SPACING = 4*VMAX + 1
FIRST_ROW = (ROWS + 1)*ROW_SPACING + 2*VMAX
LAST_ROW = FIRST_ROW + (ROWS - 1)*ROW_SPACING
K = LAST_ROW + 1
PARAMETERS = list(previous.PARAMETERS)
NAMES = list(previous.NAMES)
SYM = {name: sp.Symbol(name) for name in NAMES}
EQUALITIES = list(previous.EQUALITIES)
EQUATION_LABELS = list(previous.EQUATION_LABELS)


def make_schedule():
    schedule = []
    for target, operation, left, right in previous.SCHEDULE:
        if target == "am1":
            baseline.need((operation, left, right) == ("-", "a", 1),
                          "the existing a-1 register is moved, not copied")
            continue
        if target == "a4":
            schedule.append(("am1", "-", "a", 1))
            baseline.need((operation, left, right) == ("*", 4, "a"),
                          "the old 4a register")
            right = "am1"
        if target == "a4m5":
            baseline.need((operation, left, right) == ("-", "a4", 5),
                          "the old 4a-5 subtraction")
            right = 1
        if target == "R20":
            baseline.need(right == previous.L, "only the fixed exponent changes")
            right = L
        schedule.append((target, operation, left, right))
    baseline.need(len(schedule) == 107, "the core count is unchanged")
    return schedule


SCHEDULE = make_schedule()
NUMERAL_SCHEDULE = [
    ("lit_two", "+", 1, 1),
    ("lit_four", "*", "lit_two", "lit_two"),
    ("lit_16", "*", "lit_four", "lit_four"),
    ("lit_256", "*", "lit_16", "lit_16"),
    ("lit_65536", "*", "lit_256", "lit_256"),
    ("lit_exponent", "*", "lit_65536", "lit_65536"),
]
LITERAL_REGISTERS = {2: "lit_two", 4: "lit_four", L: "lit_exponent"}
STRICT_SCHEDULE = NUMERAL_SCHEDULE + [
    (target, operation, LITERAL_REGISTERS.get(left, left),
     LITERAL_REGISTERS.get(right, right))
    for target, operation, left, right in SCHEDULE
]


def source_residuals():
    source = list(previous.source_residuals())
    baseline.need(EQUATION_LABELS[19] == "E20", "fixed exponent equation position")
    source[19] = SYM["ka"] - L - SYM["Delta"]*(SYM["a"] - 1)
    return source


def verify_support_bounds():
    baseline.need(sp.isprime(PRIME), "the modular pair-recovery field is prime")
    residues = [i*i % PRIME for i in range(60)]
    pairs = [(i, j) for i in range(60) for j in range(i, 60)]
    for i, j in pairs:
        encoded = PLACE_MULTIPLIER*(i+j) + residues[i] + residues[j]
        pair_sum, residue_sum = divmod(encoded, PLACE_MULTIPLIER)
        baseline.need(pair_sum == i+j and residue_sum == residues[i]+residues[j],
                      "base122 recovers the exact integer index sum")
        product = (pair_sum**2 - residue_sum)*pow(2, -1, PRIME) % PRIME
        baseline.need(product == i*j % PRIME, "the field recovers the pair product")
    monomials = [0] + list(VARIABLE_WEIGHTS) + [
        VARIABLE_WEIGHTS[i] + VARIABLE_WEIGHTS[j] for i, j in pairs]
    baseline.need(len(monomials) == len(set(monomials)) == 1891,
                  "every homogeneous quadratic monomial has a distinct weight")
    baseline.need(VARIABLE_WEIGHTS[0] == 1 and VMAX == 21607, "exact variable bounds")
    baseline.need((ROW_SPACING, FIRST_ROW, LAST_ROW, K)
                  == (86429, 158467571, 316719070, 316719071), "exact row layout")
    baseline.need(ROW_SPACING > 2*VMAX, "different row support intervals are disjoint")
    baseline.need(FIRST_ROW - 2*VMAX > VMAX, "low variable tests vanish automatically")
    baseline.need(2*FIRST_ROW - 2*VMAX > LAST_ROW, "dummy coordinates miss all targets")
    baseline.need(3*K + 2 == 950157215 < 2**30 < L,
                  "the degree and high-mask margins fit below the new exponent")
    baseline.need(60 + ROWS + 1 == 1893 < 1900, "the old coefficient bound is unchanged")
    return {
        "construction": "v_i=1+3*(122*i+(i^2 mod61)), 0<=i<=59",
        "field_prime": PRIME, "place_multiplier": PLACE_MULTIPLIER,
        "original_witnesses": 58, "guard_witnesses": 1, "base_rows": 1830,
        "rows": ROWS, "positive_weight_coordinates": 60,
        "code_coordinates_excluding_input": 1892, "coordinates_including_input": 1893,
        "coefficient_bound": 1900, "input_weight": 0, "decoded_unit_weight": 1,
        "variable_weights": list(VARIABLE_WEIGHTS), "monomial_weights_distinct": 1891,
        "maximum_variable_weight": str(VMAX), "row_spacing": str(ROW_SPACING),
        "first_row_weight": str(FIRST_ROW), "last_row_weight": str(LAST_ROW),
        "short_baseline_length": str(K), "required_degree_bound": str(3*K + 2),
        "exponent": str(L),
    }


def verify_primitives(schedule, env):
    primitives = primitive_instructions(schedule)
    histogram = {"+": 0, "*": 0}
    for row in primitives:
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left, right, target = (value(row[name]) for name in ("left", "right", "result"))
        operation = row["operation"]
        baseline.need(operation in histogram, "only addition and multiplication primitives")
        expected = left + right if operation == "+" else left*right
        baseline.need(sp.expand(expected - target) == 0, "every primitive is exact")
        histogram[operation] += 1
    return primitives, histogram


def verify_certificate():
    receipt = previous.verify_certificate()
    support = verify_support_bounds()
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    s = SYM
    G_source = 1 + (s["a"] + 1)*(s["f"]**2 - 1)
    G_calculated = 1 + (s["a"] + 1)*env["AE"]
    H17 = 2*s["r"] + 1 + s["j"]*s["c"]
    corrections = {
        6: (s["la"]*source[3] - source[2])*s["q"]**2*(s["n"]**2 - 1),
        16: source[15]*(s["a"] + 1)*(G_source + G_calculated)*H17**2,
    }
    records = []
    baseline.need(len(source) == len(EQUALITIES) == 22, "22 equations and equality tests")
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left] - env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual - residual - correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual + residual) == 0:
            sign = -1
        else:
            raise AssertionError(f"residual mismatch at {EQUATION_LABELS[index]}")
        records.append({"equation": EQUATION_LABELS[index], "equality": [left, right],
                        "source_residual_polynomial": sp.sstr(sp.expand(residual)),
                        "certificate_residual_polynomial": sp.sstr(actual),
                        "source_residual_sign": sign,
                        "triangular_correction_polynomial": sp.sstr(sp.expand(correction))})
    baseline.need(sp.expand(env["a4m5"] - (4*s["a"] - 5)) == 0,
                  "the literal5 elimination preserves E14 exactly")
    primitives, primitive_histogram = verify_primitives(SCHEDULE, env)
    baseline.need(len(primitives) == 107 and primitive_histogram == {"+": 48, "*": 59},
                  "unchanged core count and histogram")
    literals = {operand for _, _, left, right in SCHEDULE for operand in (left, right)
                if isinstance(operand, int)}
    baseline.need(literals == {1, 2, 4, L}, "all remaining numerals are generated")
    numeral_env = {}
    numeral_histogram = baseline.run_schedule(NUMERAL_SCHEDULE, numeral_env)
    baseline.need([numeral_env[name] for name in LITERAL_REGISTERS.values()] == [2, 4, L],
                  "six-operation numeral chain")
    numeral_primitives, _ = verify_primitives(NUMERAL_SCHEDULE, numeral_env)
    strict_env = dict(SYM)
    strict_histogram = baseline.run_schedule(STRICT_SCHEDULE, strict_env)
    strict_primitives, strict_primitive_histogram = verify_primitives(STRICT_SCHEDULE, strict_env)
    baseline.need(len(strict_primitives) == 113 and
                  strict_primitive_histogram == {"+": 49, "*": 64}, "full113 histogram")
    strict_literals = {operand for _, _, left, right in STRICT_SCHEDULE
                       for operand in (left, right) if isinstance(operand, int)}
    baseline.need(strict_literals == {1}, "the strict schedule uses only literal1")
    for name in env:
        baseline.need(sp.expand(strict_env[name] - env[name]) == 0,
                      "strict and core registers agree exactly")
    receipt.update({
        "operations": 107, "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {"additions": 48, "multiplications": 59},
        "primitive_instructions": primitives, "equalities": EQUALITIES,
        "residual_polynomials": records, "support_bounds": support,
        "exponent_numeral": str(L),
        "numerals_from_one": {"operations": 6, "histogram": numeral_histogram,
            "primitive_instructions": numeral_primitives,
            "scope": "Generate2,4,L from1; x,Z,V,H remain supplied parameters"},
        "operations_with_numerals_from_one": 113,
        "strict_certificate": {"operations": 113, "straight_line_histogram": strict_histogram,
            "additions_and_multiplications_only": {"additions": 49, "multiplications": 64},
            "primitive_instructions": strict_primitives, "equalities": EQUALITIES,
            "only_literal": 1},
        "proofs": receipt["proofs"] + ["../1980/MODULAR_SIDON_PROOF.md"],
        "scope": "107 core arithmetic operations with the modular Sidon index;113 when literal numerals are generated from1",
        "fixed_index_override": "MODULAR_SIDON_PROOF.md replaces every earlier variable weight, row weight, K,L, and the resulting fixed Z,V,H; it preserves all support and coefficient inequalities",
    })
    return receipt


if __name__ == "__main__":
    result = verify_certificate()
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS:", result["operations"], "core operations;", result["operations_with_numerals_from_one"],
          "with numerals from1;", result["equalities"].__len__(), "equalities")
    print("Support:", VMAX, FIRST_ROW, LAST_ROW, K, L)
