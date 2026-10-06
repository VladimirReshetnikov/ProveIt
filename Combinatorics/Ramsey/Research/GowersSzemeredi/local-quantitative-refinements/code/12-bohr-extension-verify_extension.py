#!/usr/bin/env python3
"""Independent finite checks for the dense Freiman extension report.

The proof is mathematical; these checks are reproducible consistency evidence.
All pass/fail decisions use integers or fractions. Decimal square roots are
used only for human-readable displays of chi, never as a correctness oracle.

Run:
    python3 verify_extension.py

The script checks every B/S pair and every ordered pair of directions in
cyclic groups of orders 1 through 8, the entire stated rational sharpness
family with 1 <= |K| <= 12, and deterministic noisy examples. It has no
third-party dependencies and does not access the network.
"""

from __future__ import annotations

import argparse
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import time


def rational(value: Fraction | int) -> str:
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else str(value)


def chi_display(value: Fraction) -> str:
    assert 0 <= value < Fraction(1, 2)
    with localcontext() as context:
        context.prec = 70
        x = Decimal(value.numerator) / Decimal(value.denominator)
        answer = (Decimal(1) - (Decimal(1) - 2 * x).sqrt()) / 2
        return format(answer, ".18f")


def chi_strictly_less(value: Fraction, bound: Fraction) -> bool:
    """Decide chi(value) < bound by rational algebra, with no square root."""
    assert 0 <= value < Fraction(1, 2)
    if bound <= 0:
        return False
    if bound >= Fraction(1, 2):
        return True
    return value < 2 * bound * (1 - bound)


def chi_at_least(value: Fraction, bound: Fraction) -> bool:
    """Decide chi(value) >= bound exactly."""
    assert 0 <= value < Fraction(1, 2)
    if bound <= 0:
        return True
    if bound >= Fraction(1, 2):
        return False
    return value >= 2 * bound * (1 - bound)


def negative_translate(mask: int, direction: int, order: int) -> int:
    """Bit mask for A-direction in Z/orderZ."""
    direction %= order
    if not direction:
        return mask
    return ((mask >> direction) | (mask << (order - direction))) & ((1 << order) - 1)


def exhaustive_intersections(max_order: int) -> dict:
    """Check pair, chain-triple, MST-triple, and boundary metric inequalities."""
    all_groups = []
    for order in range(1, max_order + 1):
        pair_checks = 0
        triple_checks = 0
        boundary_checks = 0
        bs_pairs = 0
        positive_chain_bounds = 0
        for b_mask in range(1, 1 << order):
            n = b_mask.bit_count()
            boundary = [
                n - (b_mask & negative_translate(b_mask, t, order)).bit_count()
                for t in range(order)
            ]
            for c in range(order):
                assert boundary[c] == boundary[-c % order]
                for d in range(order):
                    assert boundary[(c + d) % order] <= boundary[c] + boundary[d]
                    boundary_checks += 1
            s_mask = b_mask
            while True:
                bs_pairs += 1
                holes = n - s_mask.bit_count()
                translated = [negative_translate(s_mask, t, order) for t in range(order)]
                for c in range(order):
                    pair_count = (s_mask & translated[c]).bit_count()
                    assert pair_count >= n - 2 * holes - boundary[c]
                    pair_checks += 1
                    for d in range(order):
                        s = (c + d) % order
                        actual = (s_mask & translated[c] & translated[s]).bit_count()
                        chain_lower = n - 3 * holes - boundary[c] - boundary[d]
                        mst_cost = min(
                            boundary[c] + boundary[d],
                            boundary[c] + boundary[s],
                            boundary[d] + boundary[s],
                        )
                        assert actual >= chain_lower
                        assert actual >= n - 3 * holes - mst_cost
                        if chain_lower > 0:
                            assert actual > 0
                            positive_chain_bounds += 1
                        triple_checks += 1
                if s_mask == 0:
                    break
                s_mask = (s_mask - 1) & b_mask
        assert bs_pairs == 3**order - 1
        all_groups.append({
            "cyclic_order": order,
            "B_S_pairs_including_empty_S": bs_pairs,
            "pair_checks": pair_checks,
            "triple_checks": triple_checks,
            "boundary_subadditivity_checks": boundary_checks,
            "strictly_positive_chain_bounds": positive_chain_bounds,
        })
    return {
        "status": "passed",
        "max_cyclic_order": max_order,
        "total_triple_checks": sum(row["triple_checks"] for row in all_groups),
        "groups": all_groups,
    }


def check_frontier(max_m: int) -> dict:
    examples = []
    for m in range(1, max_m + 1):
        for t in range(m + 1):
            S = {(r, k) for r in (0, 1) for k in range(m)}
            B = S | {(2, k) for k in range(t)}
            C = {(r, 0) for r in range(3)}
            phi = {x: x[0] for x in S}

            def add(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
                return ((x[0] + y[0]) % 3, (x[1] + y[1]) % m)

            def sub(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
                return ((x[0] - y[0]) % 3, (x[1] - y[1]) % m)

            # Equality of all pair-sums is the exact Freiman-2 condition.
            sum_values = {}
            increments = {}
            for x in S:
                for y in S:
                    total = add(x, y)
                    value = phi[x] + phi[y]
                    if total in sum_values:
                        assert sum_values[total] == value
                    sum_values[total] = value
                    difference = sub(x, y)
                    increment = phi[x] - phi[y]
                    if difference in increments:
                        assert increments[difference] == increment
                    increments[difference] = increment

            boundary = {
                c: Fraction(sum(add(x, c) not in B for x in B), len(B))
                for c in C
            }
            epsilon = Fraction(len(B - S), len(B))
            kappa = max(boundary.values())
            assert epsilon == Fraction(t, 2 * m + t)
            assert kappa == Fraction(m - t, 2 * m + t)
            assert 3 * epsilon + 2 * kappa == 1
            assert all(c in increments for c in C)
            assert increments[(0, 0)] == 0
            assert increments[(1, 0)] == 1
            assert increments[(2, 0)] == -1
            assert add((1, 0), (1, 0)) == add((2, 0), (0, 0))
            assert 2 * increments[(1, 0)] != increments[(2, 0)] + increments[(0, 0)]
            examples.append({
                "m": m,
                "t": t,
                "epsilon": rational(epsilon),
                "kappa": rational(kappa),
                "frontier": "3 epsilon + 2 kappa = 1",
                "Freiman_input": True,
                "Freiman_increment_on_C": False,
            })
    return {"status": "passed", "examples_checked": len(examples), "examples": examples}


def robust_example(
    name: str,
    order: int,
    B: set[int],
    S: set[int],
    C: set[int],
    slope: int,
    offset: int,
    corruptions: dict[int, int],
) -> dict:
    assert S and S <= B
    assert set(corruptions) <= S
    phi = {x: (slope * x + offset + corruptions.get(x, 0)) % order for x in S}
    directions = C | {(c + d) % order for c in C for d in C}
    n = len(B)
    epsilon = Fraction(n - len(S), n)
    boundary = {
        t: Fraction(sum((x + t) % order not in B for x in B), n)
        for t in C
    }
    kappa = max(boundary.values())
    eta = {}
    actual_modal_error = {}
    D = {}
    edge_sizes = {}
    for t in directions:
        edges = [x for x in S if (x + t) % order in S]
        assert edges
        labels = Counter((phi[(x + t) % order] - phi[x]) % order for x in edges)
        counts = labels.most_common()
        mode, mass = counts[0]
        assert mass * 2 > len(edges)
        D[t] = mode
        edge_sizes[t] = len(edges)
        eta[t] = 1 - sum(Fraction(count * count, len(edges) ** 2) for count in labels.values())
        actual_modal_error[t] = 1 - Fraction(mass, len(edges))
        assert 0 <= eta[t] < Fraction(1, 2)
        assert chi_at_least(eta[t], actual_modal_error[t])
        assert D[t] == slope * t % order

    eta_max = max(eta.values())
    q_actual_max = max(actual_modal_error.values())
    budget = (1 - 3 * epsilon - 2 * kappa) / 3
    assert chi_strictly_less(eta_max, budget)
    assert 3 * epsilon + 2 * kappa + 3 * q_actual_max < 1
    checked_additions = 0
    respected_sum_values = {}
    for c in C:
        for d in C:
            s = (c + d) % order
            assert (D[c] + D[d]) % order == D[s]
            triple_count = sum(
                (x + c) % order in S and (x + s) % order in S for x in S
            )
            actual_bad_budget = sum(
                actual_modal_error[t] * edge_sizes[t] for t in (c, d, s)
            )
            assert triple_count > actual_bad_budget
            total_value = (D[c] + D[d]) % order
            if s in respected_sum_values:
                assert respected_sum_values[s] == total_value
            respected_sum_values[s] = total_value
            checked_additions += 1

    result = {
        "name": name,
        "ambient_cyclic_order": order,
        "B_size": len(B),
        "S_size": len(S),
        "C_size": len(C),
        "epsilon": rational(epsilon),
        "kappa": rational(kappa),
        "max_directional_collision_defect": rational(eta_max),
        "chi_of_max_defect_decimal_display": chi_display(eta_max),
        "max_actual_modal_error": rational(q_actual_max),
        "collision_criterion_verified_exactly": True,
        "local_additions_checked": checked_additions,
        "modal_map_is_Freiman_2_on_C": True,
        "nonzero_value_corruptions": len(corruptions),
    }

    if B == set(range(order)) and C == B:
        residual = Counter((phi[x] - D[x]) % order for x in S)
        h, largest_mass = residual.most_common(1)[0]
        disagreement = 1 - Fraction(largest_mass, len(S))
        pair_defect = 1 - sum(Fraction(v * v, len(S) ** 2) for v in residual.values())
        weighted_modal_error = sum(
            actual_modal_error[t] * edge_sizes[t] for t in directions
        ) / (len(S) ** 2)
        assert weighted_modal_error == pair_defect
        assert pair_defect <= q_actual_max
        assert chi_at_least(eta_max, pair_defect)
        # chi(chi(eta)) >= disagreement is equivalent to
        # chi(eta) >= 2*disagreement*(1-disagreement).
        assert disagreement < Fraction(1, 2)
        assert chi_at_least(eta_max, 2 * disagreement * (1 - disagreement))
        result["global_affine_repair"] = {
            "homomorphism_slope": slope % order,
            "affine_offset": h,
            "agreement_fraction": rational(1 - disagreement),
            "residual_pair_disagreement": rational(pair_defect),
            "nested_chi_agreement_bound_verified_exactly": True,
        }
    else:
        result["global_affine_repair"] = "not asserted for this local example"
    return result


def robust_examples() -> dict:
    g31 = set(range(31))
    g47 = set(range(47))
    b101 = set(range(61))
    cases = [
        robust_example("full_group_one_error", 31, g31, g31, g31, 7, 4, {0: 3}),
        robust_example(
            "dense_subset_two_errors", 31, g31, g31 - {3, 7, 18},
            g31, 7, 4, {0: 3, 11: 8},
        ),
        robust_example(
            "dense_subset_seven_holes_two_errors", 47, g47,
            g47 - {3, 7, 12, 18, 26, 35, 41}, g47, 9, 5, {0: 3, 20: 11},
        ),
        robust_example(
            "local_interval_two_errors", 101, b101, b101 - {17, 42},
            {x % 101 for x in range(-2, 3)}, 7, 4, {9: 3, 36: 8},
        ),
    ]
    return {"status": "passed", "examples_checked": len(cases), "examples": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-cyclic", type=int, default=8)
    parser.add_argument("--frontier-max", type=int, default=12)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("extension_validation.json"),
    )
    args = parser.parse_args()
    if not 1 <= args.max_cyclic <= 12:
        parser.error("--max-cyclic must lie between 1 and 12; default 8 is quick")
    if args.frontier_max < 1:
        parser.error("--frontier-max must be positive")
    start = time.perf_counter()
    result = {
        "status": "passed",
        "arithmetic": "integer and Fraction pass/fail checks; Decimal display only",
        "scope": "finite consistency checks, not a replacement for mathematical proof",
        "intersection_checks": exhaustive_intersections(args.max_cyclic),
        "sharp_frontier": check_frontier(args.frontier_max),
        "robust_repair": robust_examples(),
    }
    result["elapsed_seconds"] = round(time.perf_counter() - start, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "triple_checks": result["intersection_checks"]["total_triple_checks"],
        "frontier_examples": result["sharp_frontier"]["examples_checked"],
        "robust_examples": result["robust_repair"]["examples_checked"],
        "elapsed_seconds": result["elapsed_seconds"],
        "output": str(args.output.resolve()),
    }, indent=2))


if __name__ == "__main__":
    main()
