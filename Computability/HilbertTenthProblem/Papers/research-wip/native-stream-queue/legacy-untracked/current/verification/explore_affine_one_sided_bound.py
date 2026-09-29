#!/usr/bin/env python3
"""Finite sparse alias repairs for the rejected one-sided packed bound.

This tests the mechanism in EXPLORATION_AFFINE_ONE_SIDED_BOUND.md,
not a replacement certificate or a full auxiliary-Pell counterexample.
No integer B**target is constructed.
"""
from collections import defaultdict
import json
from pathlib import Path

import round32_1980_affine_radix_encoding as code

HERE = Path(__file__).resolve().parent


def verify():
    layout = code.make_layout()
    code.symbolic_checks(layout)
    positions = code.positions_to_inspect(layout)
    cases = []
    for x in range(1, 17):
        logical = {"x": x, "delta": 1, "X": x, "Y": x, "Z": x,
                   "delta_copy": 1, "u": x*x-1, "v": x*x+1,
                   "a": x+2, "z": 0, "zero": 1}
        values = code.physical_assignment(layout, logical, 64)
        B = code.next_power_two(max(128+x, 16*sum(values.values())**2, 32*x*x+1))
        code.first_mask_check(layout, values, 64, B)
        raw = code.numeric_raw_low(layout, values)
        before, _, _ = code.sparse_digits(raw, positions, B)
        failed_before = sum(any(before[t+j]["digit"] >= 4 for j in range(3))
                            for t in layout["targets"])
        code.need(failed_before > 0, "the original circuit really fails the target masks")
        patch = defaultdict(int)
        for target in layout["targets"][:-3]:
            code.need(before[target]["incoming"] == 0, "the original target starts with reset carry zero")
            correction = (-raw.get(target, 0)) % (B**3)
            for j in range(3):
                patch[target+j] += correction % B
                correction //= B
        patch = {degree: coefficient for degree, coefficient in patch.items() if coefficient}
        code.need(patch and max(patch) < layout["K"], "all repairs are below the short-code cutoff")
        code.need(all(0 <= coefficient < B for coefficient in patch.values()), "repair digits do not overlap")
        adjusted = defaultdict(int, raw)
        for degree, coefficient in patch.items():
            adjusted[degree] += coefficient
        after, events, _ = code.sparse_digits(adjusted, positions, B)
        for target in layout["targets"][:-3]:
            code.need(after[target]["incoming"] == 0, "earlier repair carries are erased by the next reset")
            code.need(all(after[target+j]["digit"] == 0 for j in range(3)), "each failed equation now has a zero window")
        for target in layout["targets"][-3:]:
            code.need([after[target+j]["digit"] for j in range(3)] == [1, 0, 0], "unit tests remain unchanged")
        code.need(all(after[position]["digit"] < 4 for position in layout["indicator"]), "all third-mask tests pass after repair")
        modulus = B//4-1
        residue = sum(coefficient*pow(B, degree, modulus)
                      for degree, coefficient in patch.items()) % modulus
        high_degree = layout["K"]+1
        high_coefficient = (-residue*pow(pow(B, high_degree, modulus), -1, modulus)) % modulus
        code.need((residue+high_coefficient*pow(B, high_degree, modulus)) % modulus == 0,
                  "an untested high digit enforces the exact congruence")
        cases.append({"x": x, "B": B, "failed_windows_before": failed_before,
                      "ordinary_windows_repaired": len(layout["targets"])-3,
                      "low_patch_digits": len(patch), "high_patch_degree": high_degree,
                      "high_patch_coefficient": high_coefficient,
                      "odd_part_of_theta": modulus, "sparse_events": events})
    return {"status": "PASS", "scope": "finite full sparse-code repairs and modular high correction; not a universal-equivalence or full Pell-witness assertion",
            "proof_note": "../1980/EXPLORATION_AFFINE_ONE_SIDED_BOUND.md",
            "cases": cases, "no_B_to_target_integer_constructed": True}


if __name__ == "__main__":
    result = verify()
    HERE.joinpath("explore_affine_one_sided_bound.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(result["status"], len(result["cases"]), "complete sparse repairs; each has 18 corrected ordinary windows")
