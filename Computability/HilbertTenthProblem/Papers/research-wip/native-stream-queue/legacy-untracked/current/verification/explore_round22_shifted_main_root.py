#!/usr/bin/env python3
"""Exact circuit accounting for two positive shifts of the main Pell root.

Exploration only. This does not modify or improve the frozen 102-operation
certificate. Fixed numerals are free. It checks all source residuals, including
the existing triangular corrections, after the stated coordinate substitution.
"""
from __future__ import annotations

import sympy as sp

import round22_1980_composed_certificate as reference
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives


def candidate(shift: int, factored_norm: bool, direct_signed_root: bool = False):
    assert shift in (0, 3)
    source_schedule = reference.SCHEDULE
    schedule = []
    for target, operation, left, right in source_schedule:
        if target == "D1":
            continue
        if shift == 3 and target == "am1":
            continue
        if target == "cam2":
            if shift == 3:
                schedule.append(("am1", "+", "a", 3))
                left, right = "c", "am1"
            schedule.append((target, operation, left, right))
            if factored_norm:
                schedule.extend([
                    ("twice_shift_product", "*", 2, "cam2"),
                    ("root_norm_factor", "+", "eps", "twice_shift_product"),
                ])
            continue
        if target == "R14":
            schedule.append((target, "+", "wn2", "gam"))
            if shift == 3:
                schedule.extend([
                    ("three_c", "*", 3, "c"),
                    ("shifted_exponent_left", "+", "eps", "three_c"),
                ])
            if not (factored_norm and direct_signed_root):
                schedule.append(("shifted_d", "+", "eps", "cam2"))
            continue
        if target == "Ac2" and factored_norm:
            if shift == 0:
                schedule.append((target, "*", "a4m5", "c2"))
            else:
                schedule.append((target, "*", "twice_shift_product", "c"))
            continue
        if target == "L15" and factored_norm:
            schedule.append((target, "*", "eps", "root_norm_factor"))
            continue
        if target == "dof" and factored_norm and direct_signed_root:
            schedule.extend([
                ("of_minus_eps", "-", "of", "eps"),
                (target, "-", "of_minus_eps", "cam2"),
            ])
            continue
        left = "shifted_d" if left == "d" else left
        right = "shifted_d" if right == "d" else right
        schedule.append((target, operation, left, right))

    equalities = list(reference.EQUALITIES)
    equalities[13] = ("eps" if shift == 0 else "shifted_exponent_left", "R14")
    names = ["eps" if name == "d" else name for name in reference.NAMES]
    symbols = {name: sp.Symbol(name) for name in names}
    env = dict(symbols)
    histogram = baseline.run_schedule(schedule, env)
    primitives, primitive_histogram = verify_primitives(schedule, env)
    old = reference.SYM
    replacement = symbols["eps"] + (old["a"] + shift)*old["c"]
    source = [sp.expand(r.subs(old["d"], replacement))
              for r in reference.source_residuals()]
    A = old["a"] + 4
    G_source = 1 + (A + 1)*(old["f"]**2 - 1)
    G_calculated = 1 + (A + 1)*env["AE"]
    H17 = 2*old["r"] + 1 + old["j"]*old["c"]
    corrections = {
        6: (old["la"]*source[3] - source[2])*old["q"]**2*(old["n"]**2 - 1),
        16: source[15]*(A + 1)*(G_source + G_calculated)*H17**2,
    }
    for index, ((left, right), residual) in enumerate(zip(equalities, source)):
        actual = sp.expand(env[left] - env[right])
        correction = corrections.get(index, sp.Integer(0))
        baseline.need(
            sp.expand(actual - residual - correction) == 0
            or (correction == 0 and sp.expand(actual + residual) == 0),
            f"shift {shift}, factored={factored_norm}: residual {index}",
        )
    expected = 102 + 2*(shift == 3) + 2*factored_norm
    baseline.need(len(primitives) == expected, "exact complete circuit count")
    return {
        "shift": shift,
        "root": f"eps=d-c*(a+{shift})",
        "factored_main_norm": factored_norm,
        "direct_signed_root": direct_signed_root,
        "instructions": len(primitives),
        "histogram": histogram,
        "primitive_histogram": primitive_histogram,
        "equalities": len(equalities),
        "positive_unknowns": len(names) - len(reference.PARAMETERS),
    }


if __name__ == "__main__":
    for shift in (0, 3):
        for factored, direct in ((False, False), (True, False), (True, True)):
            print(candidate(shift, factored, direct))
    print("PASS: all six complete schedules have the exact transformed residuals.")
