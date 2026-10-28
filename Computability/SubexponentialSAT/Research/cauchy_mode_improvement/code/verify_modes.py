"""Targeted exact-arithmetic checks for cauchy_modes.py (standard library only).

Run from the archive root: python3 code/verify_modes.py
Results are written to results/verification.json. These finite checks test
algebra and implementation, not the correctness of a complete SAT solver
or the asymptotic analysis of the upstream paper.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import platform
import sys

from cauchy_modes import (
    F4Ring, Mod2Ring, actual_deformation_data, check_skeleton_domain,
    count_weighted_tuples, factorial_valuation2, kernel_fraction, kernel_mod,
    mode_weight, reconstruct_fraction, reconstruct_mod, source_mod,
    target_fraction, target_mod, valuation2_integer,
)


def valuation_fraction(value):
    if not value: return float("inf")
    return valuation2_integer(value.numerator) - valuation2_integer(value.denominator)


def exact_rational_tests(stats):
    zs = tuple(map(Fraction, ("2/3", "6/5", "14/17", "4/7", "8/9")))
    for J in (1, 2, 4, 8, 16):
        for z in zs:
            for j in range(J):
                expected = kernel_fraction(Fraction(2), z, j)
                for family in ("newton", "skeleton"):
                    actual = reconstruct_fraction(Fraction(2), z, j, J, family)
                    assert actual == expected, (J, z, j, family)
                    stats["exact_rational_kernel_identities"] += 1
            for b in range(J):
                for family in ("geometric", "newton", "skeleton"):
                    coefficient = target_fraction(Fraction(2), z, b, family)
                    assert valuation_fraction(coefficient) >= mode_weight(b, family)
                    stats["exact_rational_target_valuations"] += 1


def scalar_modular_tests(stats):
    for precision in (1, 2, 3, 5, 9, 17, 40):
        ring = Mod2Ring(precision)
        for J in (1, 2, 4, 8, 16):
            for z_integer in (0, 2, 4, 6, 14):
                c, z = ring.integer(2), ring.integer(z_integer)
                for j in range(J):
                    expected = kernel_mod(ring, c, z, j)
                    for family in ("geometric", "newton", "skeleton"):
                        assert reconstruct_mod(ring, c, z, j, J, family) == expected
                        stats["scalar_modular_truncated_identities"] += 1


def actual_extension_tests(stats):
    # Real grid deformation T=t+2^(a+1) U; includes all i<a, different
    # denominator valuations, negative nodes, and high precision.
    observed_denominator_valuations = set()
    for precision in (8, 17, 64, 192):
        ring = F4Ring(precision)
        for a in range(1, 7):
            L = 1 << a
            for i in range(a):
                for sign in (1, -1):
                    t = sign * (1 << i)
                    W, crossing = actual_deformation_data(ring, a, t)
                    for x in sorted({0, L//3, L-1}):
                        high_bit = ((x >> i) & 1) << i
                        y0s = {x % (1 << (i+1)), high_bit,
                               high_bit + (1 << i) - 1}
                        for y0 in sorted(y0s):
                            c, z, J = crossing(x, y0)
                            observed_denominator_valuations.add(valuation2_integer(t-y0+x))
                            for b in range(J):
                                for family in ("geometric", "newton", "skeleton"):
                                    coefficient = target_mod(ring, c, z, b, family)
                                    assert ring.valuation(coefficient) >= min(precision, mode_weight(b, family))
                                    stats["actual_extension_target_valuations"] += 1
                            js = {0, J//2, J-1}
                            if J > 1: js.add(1)
                            for j in sorted(js):
                                expected = W(x, y0 + (1 << (i+1))*j)
                                assert kernel_mod(ring, c, z, j) == expected
                                stats["actual_deformation_to_kernel_checks"] += 1
                                for family in ("geometric", "newton", "skeleton"):
                                    value = reconstruct_mod(ring, c, z, j, J, family, truncate=True)
                                    assert value == expected, (precision, a, i, sign, x, y0, j, family)
                                    stats["actual_extension_truncated_identities"] += 1
    stats["denominator_valuations_covered"] = sorted(observed_denominator_valuations)


def bad_domain_regression(stats):
    ring = F4Ring(192)
    z = ring.scale(ring.generator, 2)
    coefficient = target_mod(ring, ring.integer(2), z, 2, "skeleton")
    actual, claimed = ring.valuation(coefficient), mode_weight(2, "skeleton")
    assert actual == 4 and claimed == 5
    try:
        check_skeleton_domain(ring, ring.integer(2), z, 4)
    except ValueError:
        stats["invalid_extension_domain_rejections"] += 1
    else:
        raise AssertionError("invalid extension input was not rejected")
    for test_ring in (ring, Mod2Ring(12)):
        try:
            test_ring.inv_unit(test_ring.integer(2))
        except ValueError:
            stats["nonunit_inverse_rejections"] += 1
        else:
            raise AssertionError("a nonunit was inverted")
    return {"row_parameter": "z=2U", "mode_index": 2,
            "actual_target_valuation": actual, "invalid_claimed_weight": claimed,
            "meaning": "Evenness alone in an extension ring is insufficient; row congruence is required."}


def contraction_check(precision, sign, family, stats):
    """A whole three-port deformed contraction, including local terms.

    Three real slots are retained from an eight-slot packet. The two
    arbitrary tensors are small integer tables; they need not be SAT
    tensors. The expanded calculation truncates after every multiplication
    according to mode weights, then substitutes source linear forms.
    """
    ring = F4Ring(precision)
    a, i, t = 3, 0, sign
    row_slots = (0, 2, 1)
    col_slots = (0, 4, 1)
    W, crossing = actual_deformation_data(ring, a, t)
    J = 1 << (a-i-1)
    tiles = sorted({y % (1 << (i+1)) for y in col_slots})
    modes = [(y0, b) for y0 in tiles for b in range(J)]
    index = {mode: at for at, mode in enumerate(modes)}
    weights = [mode_weight(b, family) for _, b in modes]
    zero_tuple = (0,) * len(modes)
    direct = expanded = ring.zero
    peak_terms = 0

    for X in product((0, 1), repeat=len(col_slots)):
        xm = sum(bit << j for j, bit in enumerate(X))
        tensor_B = ring.integer(3 + xm*xm)
        sources = []
        for y0, b in modes:
            value = ring.zero
            for y, bit in zip(col_slots, X):
                if bit and y % (1 << (i+1)) == y0:
                    j = y // (1 << (i+1))
                    value = ring.add(value, source_mod(ring, j, b, family))
            sources.append(value)
        source_powers = [[ring.power(v, degree) for degree in range(4)] for v in sources]

        for Y in product((0, 1), repeat=len(row_slots)):
            ym = sum(bit << j for j, bit in enumerate(Y))
            tensor_A = ring.integer(1 + 2*ym)
            multiplier = ring.mul(tensor_A, tensor_B)
            direct_product = ring.one
            polynomial = {zero_tuple: ring.one}

            for x, ybit in zip(row_slots, Y):
                row_value = local_value = ring.zero
                for y, xbit in zip(col_slots, X):
                    if not xbit: continue
                    entry = W(x, y)
                    row_value = ring.add(row_value, entry)
                    if ((x >> i) & 1) != ((y >> i) & 1):
                        local_value = ring.add(local_value, entry)
                affine_value = row_value if ybit else ring.sub(ring.one, row_value)
                direct_product = ring.mul(direct_product, affine_value)
                constant = local_value if ybit else ring.sub(ring.one, local_value)
                row_modes = []
                for y0 in tiles:
                    if ((x >> i) & 1) != ((y0 >> i) & 1): continue
                    c, z, _ = crossing(x, y0)
                    for b in range(J):
                        if mode_weight(b, family) >= precision: continue
                        coefficient = target_mod(ring, c, z, b, family)
                        if not ybit: coefficient = ring.scale(coefficient, -1)
                        row_modes.append((index[(y0, b)], coefficient))

                updated = {}
                for exponents, coefficient in polynomial.items():
                    if constant != ring.zero:
                        value = ring.mul(coefficient, constant)
                        updated[exponents] = ring.add(updated.get(exponents, ring.zero), value)
                    current_weight = sum(w*e for w, e in zip(weights, exponents))
                    for k, row_coefficient in row_modes:
                        if current_weight + weights[k] >= precision: continue
                        new_exponents = list(exponents); new_exponents[k] += 1
                        key = tuple(new_exponents)
                        value = ring.mul(coefficient, row_coefficient)
                        updated[key] = ring.add(updated.get(key, ring.zero), value)
                polynomial = {e: v for e, v in updated.items() if v != ring.zero}
                peak_terms = max(peak_terms, len(polynomial))

            evaluated = ring.zero
            for exponents, coefficient in polynomial.items():
                term = coefficient
                for k, exponent in enumerate(exponents):
                    if exponent: term = ring.mul(term, source_powers[k][exponent])
                evaluated = ring.add(evaluated, term)
            assert evaluated == direct_product, (precision, sign, family, X, Y)
            stats["affine_product_assignment_checks"] += 1
            direct = ring.add(direct, ring.mul(multiplier, direct_product))
            expanded = ring.add(expanded, ring.mul(multiplier, evaluated))
    assert direct == expanded
    stats["complete_tiny_contraction_checks"] += 1
    return {"precision": precision, "node_sign": sign, "family": family,
            "real_row_ports": len(row_slots), "real_column_ports": len(col_slots),
            "residue_in_F4_ring": list(direct), "peak_retained_polynomial_terms": peak_terms}


def main():
    stats = {k: 0 for k in (
        "exact_rational_kernel_identities", "exact_rational_target_valuations",
        "scalar_modular_truncated_identities", "actual_extension_target_valuations",
        "actual_deformation_to_kernel_checks", "actual_extension_truncated_identities",
        "invalid_extension_domain_rejections", "nonunit_inverse_rejections",
        "affine_product_assignment_checks", "complete_tiny_contraction_checks")}
    exact_rational_tests(stats)
    scalar_modular_tests(stats)
    actual_extension_tests(stats)
    counterexample = bad_domain_regression(stats)
    contractions = [contraction_check(p, sign, family, stats)
                    for p in (5, 9, 17, 32) for sign in (1, -1)
                    for family in ("newton", "skeleton")]
    diagnostics = []
    for p in (48, 80, 128):
        counts = {family: count_weighted_tuples(p, 2, 32, family)
                  for family in ("geometric", "newton", "skeleton")}
        assert counts["skeleton"] <= counts["newton"] <= counts["geometric"]
        diagnostics.append({"precision": p, "colors": 2, "modes_per_color": 32,
                            "tuple_counts": counts})
    result = {"status": "PASS", "python_version": platform.python_version(),
              "scope": "Exact local algebra, weight truncation, and tiny tensor contractions; not a full SAT implementation or an asymptotic benchmark.",
              "counts": stats, "extension_ring": "(Z/2^p)[U]/(U^2+U+1)",
              "actual_grid_parameters": {"a": "1 through 6", "i": "all 0 <= i < a", "nodes": "+/-2^i", "precisions": [8,17,64,192]},
              "invalid_domain_regression": counterexample,
              "tiny_contractions": contractions,
              "finite_partition_diagnostics": diagnostics,
              "diagnostic_note": "Partition counts use the same finite 32-mode cap for all three families. They are not measured SAT running times."}
    destination = Path(__file__).resolve().parents[1] / "results" / "verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": stats,
                      "results_path": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
