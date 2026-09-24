#!/usr/bin/env python3
"""Verified 127-, 126-, and 123-operation certificates.

The three algebraic savings are independent:

* share V = (w n^2)(r s n^2) in a = V + r s n^2 and
  p = 2 V (r s n^2), saving one multiplication;
* use E2 and E3 to replace 1 + theta lambda in E7 by
  lambda + q^4 - 2 z lambda, saving one multiplication after factoring;
* replace c = 2 r + 1 + kappa + phi by c = kappa + phi, with phi positive,
  saving one addition. Positive Pell solutions automatically restore the
  discarded gap; see ../1980/PELL_GAP_PROOF.md for the exact proof.

The E7 verification records an explicit triangular residual identity rather
than silently treating equality modulo preceding equations as a polynomial
identity. The phi reparameterization is checked in both directions. The
positivity implication in the third saving is a mathematical proof, not a
claim established by testing samples or symbolic polynomial expansion.

The 127 variant verifies the original positive-integer system pointwise,
retaining its original phi. The 126 variant changes phi by a proved positive
slack reparameterization. The 123 variant applies all three savings to the
126-operation recoding of round4_1980_recoded_certificate.py; its admissible
input encoding is different, with the proof in ../1980/RECODING_PROOF.md.

Run this file directly to write round4_1980_optimized_certificate.json,
including every primitive addition/multiplication instruction and equality.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

import round4_1980_operation_count as baseline
import round4_1980_recoded_certificate as recoded

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_optimized_certificate.json"


def replace_block(schedule, targets, replacement):
    """Replace an exactly identified consecutive block, rejecting drift."""
    starts = [i for i, row in enumerate(schedule) if row[0] == targets[0]]
    baseline.need(len(starts) == 1, f"unique start for {targets}")
    start = starts[0]
    baseline.need(
        [row[0] for row in schedule[start:start + len(targets)]] == targets,
        f"baseline block changed: {targets}",
    )
    schedule[start:start + len(targets)] = replacement


def optimize_schedule(source_schedule, *, recoding=False, shorten_gap=True):
    schedule = list(source_schedule)
    baseline.need(len(schedule) == (126 if recoding else 129), "source schedule count")

    if not recoding:
        replace_block(schedule, ["zl", "ezl", "t2"], [
            ("Zla", "*", "z2", "la"),
            ("e2", "*", 2, "e"),
            ("t2", "-", "e2", "Zla"),
        ])
    doubled_z_lambda = "zl" if recoding else "Zla"
    replace_block(schedule, [
        "bl", "q3bl", "T1", "thl", "thlq3", "T2", "b5m2", "b5m2q8", "T",
    ], [
        ("Tcoef", "-", "L2", doubled_z_lambda),
        ("Tq3", "*", "Tcoef", "q3"),
        ("bm1", "-", "b", 1),
        ("lbm1", "*", "l", "bm1"),
        ("T2", "-", "Tq3", "lbm1"),
        ("b5m2", "-", "B" if recoding else "b5", 2),
        ("b5m2q8", "*", "b5m2", "q8"),
        ("T", "+", "T2", "b5m2q8"),
    ])
    replace_block(schedule, [
        "wn2", "wn2p1", "sn2", "rsn2", "R12", "rsn2sq", "wsq", "R8",
    ], [
        ("wn2", "*", "w", "n2"),
        ("sn2", "*", "s", "n2"),
        ("rsn2", "*", "r", "sn2"),
        ("UM", "*", "wn2", "rsn2"),
        ("R12", "+", "UM", "rsn2"),
        ("wsq", "*", "UM", "rsn2"),
        ("R8", "*", 2, "wsq"),
    ])
    if shorten_gap:
        replace_block(schedule, ["tk", "R13"], [
            ("R13", "+", "ka", "phi"),
        ])
    expected = (126 if recoding else 129) - 2 - int(shorten_gap)
    baseline.need(len(schedule) == expected, "expected algebraic savings")
    return schedule


SCHEDULE = optimize_schedule(baseline.SCHEDULE)
EQUALITIES = list(baseline.EQUALITIES)
ORIGINAL_SYSTEM_SCHEDULE = optimize_schedule(baseline.SCHEDULE, shorten_gap=False)
COMBINED_SCHEDULE = optimize_schedule(recoded.SCHEDULE, recoding=True)
COMBINED_EQUALITIES = list(recoded.EQUALITIES)


def primitive_instructions(schedule):
    """Serialize true u + v = t or u * v = t statements, never subtraction."""
    return [
        {"operation": "+" if op == "-" else op,
         "left": target if op == "-" else left,
         "right": right,
         "result": left if op == "-" else target}
        for target, op, left, right in schedule
    ]


def verify_recoded_constants():
    schedule = [
        ("two", "+", 1, 1), ("four", "+", "two", "two"),
        ("five", "+", "four", 1),
        ("f2", "*", "five", "five"), ("f3", "*", "f2", "five"),
        ("f6", "*", "f3", "f3"), ("f7", "*", "f6", "five"),
        ("f13", "*", "f7", "f6"), ("f26", "*", "f13", "f13"),
        ("f52", "*", "f26", "f26"), ("f59", "*", "f52", "f7"),
    ]
    env = {}
    histogram = baseline.run_schedule(schedule, env)
    baseline.need(env["f59"] == recoded.L, "recoded exponent constant")
    return {"operations": len(schedule), "histogram": histogram,
            "note": "2,4,5 from 1; addition chain 1,2,3,6,7,13,26,52,59 for 5^59",
            "primitive_instructions": primitive_instructions(schedule)}


def verify_variant(*, recoding=False, shorten_gap=True):
    module = recoded if recoding else baseline
    schedule = optimize_schedule(module.SCHEDULE, recoding=recoding, shorten_gap=shorten_gap)
    equalities = module.EQUALITIES
    s = module.SYM
    env = dict(s)
    histogram = baseline.run_schedule(schedule, env)
    source = module.source_residuals()
    offset = int(recoding)
    modified = list(source)
    if shorten_gap:
        modified[12 + offset] = s["c"] - s["ka"] - s["phi"]

    expected_correction = (s["la"] * source[2 + offset] - source[1 + offset]) * s["q"]**3 * (s["n"]**2 - 1)
    signs = []
    for i, ((left, right), residual) in enumerate(zip(equalities, modified)):
        actual = sp.expand(env[left] - env[right])
        if i == 6 + offset:
            baseline.need(
                sp.expand(actual - residual - expected_correction) == 0,
                "E7 triangular identity: F7new = F7old + (lambda F3 - F2)q^3(n^2-1)",
            )
            signs.append(1)
        elif sp.expand(actual - residual) == 0:
            signs.append(1)
        elif sp.expand(actual + residual) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"equation E{i + 1}: unexpected residual")

    # These are the exact maps between systems. Their positivity is proved
    # separately using the elementary Pell gap argument, not by SymPy.
    if shorten_gap:
        tr1 = 2 * s["r"] + 1
        forward = source[12 + offset].subs(s["phi"], s["phi"] - tr1)
        backward = modified[12 + offset].subs(s["phi"], s["phi"] + tr1)
        baseline.need(sp.expand(forward - modified[12 + offset]) == 0, "new phi to old phi")
        baseline.need(sp.expand(backward - source[12 + offset]) == 0, "old phi to new phi")
    total = (126 if recoding else 129) - 2 - int(shorten_gap)
    baseline.need(sum(histogram.values()) == total, "optimized count")
    baseline.need(len(equalities) == len(source) == 20 + offset, "equality count")

    used = {
        operand for _, _, left, right in schedule
        for operand in (left, right) if isinstance(operand, str)
    }
    used |= {name for pair in equalities for name in pair}
    baseline.need(set(module.NAMES) <= used, "all source variables remain represented")

    constants = verify_recoded_constants() if recoding else baseline.verify_constants()
    result = {
        "status": "PASS",
        "baseline_operations": 129,
        "operations": total,
        "straight_line_histogram": histogram,
        "additions_and_multiplications_only": {
            "additions": histogram["+"] + histogram["-"],
            "multiplications": histogram["*"],
        },
        "equality_tests": len(equalities),
        "unknowns": 33 if recoding else 32,
        "parameters": ["x", "Z", "u", "y", "H"] if recoding else ["x", "z", "u", "y"],
        "positive_input_names": module.NAMES,
        "auxiliary_domain": "integers, including negative integers",
        "residual_signs": signs,
        "triangular_identity": "F7new = F7old + (lambda F3 - F2)q^3(n^2 - 1)",
        "phi_maps": {
            "old_from_new": "phi_old = phi_new - (2r + 1)",
            "new_from_old": "phi_new = phi_old + (2r + 1)",
            "positivity_proof": "../1980/PELL_GAP_PROOF.md",
        } if shorten_gap else "unchanged",
        "numerals_from_one": constants,
        "operations_with_numerals_from_one": total + constants["operations"],
        "primitive_instructions": primitive_instructions(schedule),
        "equalities": equalities,
        "scope": ("recoded admissible indices; not pointwise equivalence to the original tuples"
                  if recoding else "original system with positive phi reparameterization"
                  if shorten_gap else "original system with all original witness values unchanged"),
        "optimality_claimed": False,
    }
    baseline.need(all(row["operation"] in {"+", "*"}
                      for row in result["primitive_instructions"]), "primitive operations only")
    for instruction in result["primitive_instructions"]:
        def value(operand):
            return sp.Integer(operand) if isinstance(operand, int) else env[operand]
        left = value(instruction["left"])
        right = value(instruction["right"])
        target = value(instruction["result"])
        computed = left + right if instruction["operation"] == "+" else left * right
        baseline.need(sp.expand(computed - target) == 0,
                      "serialized primitive instruction is exactly the scheduled identity")
    return result


def verify_certificate():
    """Preserve the original public entry point for the 126 variant."""
    return verify_variant()


def main():
    result = {
        "status": "PASS",
        "original_system_127": verify_variant(shorten_gap=False),
        "reparameterized_system_126": verify_variant(),
        "recoded_system_123": verify_variant(recoding=True),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    for name, certificate in result.items():
        if isinstance(certificate, dict):
            print(name, certificate["status"], certificate["operations"],
                  certificate["straight_line_histogram"],
                  "including numeral construction:", certificate["operations_with_numerals_from_one"])
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
