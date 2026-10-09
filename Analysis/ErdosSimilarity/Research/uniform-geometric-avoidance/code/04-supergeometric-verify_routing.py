#!/usr/bin/env python3
"""Independent finite checks for the growing-branching routing argument.

Run: python3 verify_routing.py --json verification_results.json

The checks deliberately target conditioning, terminal-address collisions,
periodic half-open boundaries, and the window budget.  They corroborate finite
lemmas; they do not replace the proof of an infinite-sequence theorem or certify
literature novelty.  Only Python's standard library is required.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def bit_vectors(size: int):
    return itertools.product((0, 1), repeat=size)


def shared_route_miss_probability(exposed_route: int | None = None) -> Fraction:
    """Enumerate every relevant outcome, including selector-dependent leaves.

    Four independent fair gates are grouped into two children.  The two tests
    under each child share an internal routing bit.  Each of the two candidate
    leaves has two *different* terminal addresses, one per test.  Every terminal
    bit has Bernoulli-1/3 law.  An optional center exposure fixes the first
    child's shared routing bit.  Gate addresses avoid exposed center addresses.

    Sharing internal routing entries is permitted in this abstract check; the
    relevant fact is that selected terminal addresses remain distinct after all
    selectors are fixed.  This directly challenges the order of conditioning.
    """
    numerator = 0
    selector_count = 0
    for gates in bit_vectors(4):
        for routes in bit_vectors(2):
            if exposed_route is not None and routes[0] != exposed_route:
                continue
            selector_count += 1
            addresses = [4 * i + 2 * routes[i] + n for i in range(2) for n in range(2)]
            assert len(set(addresses)) == 4
            for terminals in bit_vectors(8):
                if all(not gates[j] or not terminals[addresses[j]] for j in range(4)):
                    # A zero terminal has weight 2/3, and a one has weight 1/3.
                    numerator += 2 ** (8 - sum(terminals))
    return Fraction(numerator, selector_count * 3**8)


def verify_conditioning() -> dict:
    expected = Fraction(5, 6) ** 4
    observed = {
        "unexposed_routes": shared_route_miss_probability(),
        "first_route_exposed_zero": shared_route_miss_probability(0),
        "first_route_exposed_one": shared_route_miss_probability(1),
    }
    assert all(value == expected for value in observed.values())

    # Negative control: two independent gates now use the SAME terminal entry.
    collision_numerator = 0
    for gate_1, gate_2, terminal in bit_vectors(3):
        if not (gate_1 and terminal) and not (gate_2 and terminal):
            collision_numerator += 1 if terminal else 2
    collision = Fraction(collision_numerator, 4 * 3)
    collision_formula = 1 - Fraction(3, 4) * Fraction(1, 3)
    false_independence_formula = Fraction(5, 6) ** 2
    assert collision == collision_formula
    assert collision != false_independence_formula

    # Another negative control: reusing the center's exposed zero gate prevents
    # that test from ever succeeding, so the nominal Bernoulli-p/2 law is false.
    exposed_zero_gate_miss = Fraction(1)
    assert exposed_zero_gate_miss != Fraction(5, 6)
    return {
        "expected_four_test_miss": rational_string(expected),
        "exact_enumerations": {key: rational_string(value) for key, value in observed.items()},
        "total_full_outcomes_unconditioned": 2**14,
        "terminal_collision_negative_control": {
            "actual_miss": rational_string(collision),
            "incorrect_independence_prediction": rational_string(false_independence_formula),
        },
        "exposed_gate_negative_control": {
            "actual_miss": rational_string(exposed_zero_gate_miss),
            "incorrect_fresh_gate_prediction": "5/6",
        },
        "passed": True,
    }


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def periodic_key(value: Fraction, resolution: int) -> int:
    # This formula also implements the right-cell rule at negative and wrapped
    # grid boundaries, with no floating-point approximation.
    return floor_fraction(resolution * value) % resolution


def key_vector(center: Fraction, t: Fraction, points, resolutions) -> tuple[int, ...]:
    return tuple(periodic_key(center + t * a, q) for a, q in zip(points, resolutions))


def boundary_representatives(center: Fraction, points, resolutions):
    boundary_values = {Fraction(1), Fraction(2)}
    for point, resolution in zip(points, resolutions):
        assert point != 0
        lower_value = min(center + point, center + 2 * point)
        upper_value = max(center + point, center + 2 * point)
        first = ceil_fraction(resolution * lower_value)
        last = floor_fraction(resolution * upper_value)
        for grid_integer in range(first, last + 1):
            t = (Fraction(grid_integer, resolution) - center) / point
            assert 1 <= t <= 2
            boundary_values.add(t)
    boundaries = sorted(boundary_values)
    representatives = set(boundaries)
    representatives.update((left + right) / 2 for left, right in zip(boundaries, boundaries[1:]))
    return boundaries, sorted(representatives)


def verify_boundary_representatives() -> dict:
    centers = [Fraction(0), Fraction(1, 256), Fraction(3, 5), Fraction(127, 128), Fraction(-1, 64)]
    points = [Fraction(1, 17), Fraction(1, 31), Fraction(1, 67)]
    resolutions = [128, 256, 512]
    interval_checks = 0
    boundary_checks = 0
    total_representatives = 0
    for center in centers:
        boundaries, representatives = boundary_representatives(center, points, resolutions)
        total_representatives += len(representatives)
        count_bound = 4 + 2 * sum(1 + point * q for point, q in zip(points, resolutions))
        assert len(representatives) <= count_bound
        represented_vectors = {
            key_vector(center, t, points, resolutions) for t in representatives
        }
        for left, right in zip(boundaries, boundaries[1:]):
            midpoint_vector = key_vector(center, (left + right) / 2, points, resolutions)
            for weight in (Fraction(1, 10), Fraction(1, 3), Fraction(2, 3), Fraction(9, 10)):
                t = (1 - weight) * left + weight * right
                assert key_vector(center, t, points, resolutions) == midpoint_vector
                interval_checks += 1
        for index, boundary in enumerate(boundaries[1:-1], 1):
            epsilon = min(boundary - boundaries[index - 1], boundaries[index + 1] - boundary) / 10
            at_boundary = key_vector(center, boundary, points, resolutions)
            just_right = key_vector(center, boundary + epsilon, points, resolutions)
            just_left = key_vector(center, boundary - epsilon, points, resolutions)
            assert at_boundary == just_right  # Exact half-open convention.
            assert just_left != just_right    # At least one recorded key changes.
            assert at_boundary in represented_vectors
            boundary_checks += 1
        # A second, unrelated rational mesh must also be covered by the same
        # deterministic representative set, independent of all random tables.
        for numerator in range(258):
            t = 1 + Fraction(numerator, 257)
            assert key_vector(center, t, points, resolutions) in represented_vectors
    return {
        "centers_including_negative_and_period_wrap": len(centers),
        "exact_open_interval_samples_checked": interval_checks,
        "exact_boundary_checks": boundary_checks,
        "total_representatives": total_representatives,
        "unrelated_mesh_samples_checked": len(centers) * 258,
        "passed": True,
    }


def verify_signed_boundaries() -> dict:
    points = [Fraction(1, 16), Fraction(-1, 16)]
    resolutions = [64, 64]
    centers = [Fraction(0), Fraction(1, 128), Fraction(127, 128)]
    genuinely_new_boundary_vectors = 0
    orientation_checks = 0
    for center in centers:
        boundaries, representatives = boundary_representatives(center, points, resolutions)
        for index, boundary in enumerate(boundaries[1:-1], 1):
            epsilon = min(boundary - boundaries[index - 1], boundaries[index + 1] - boundary) / 10
            at_boundary = key_vector(center, boundary, points, resolutions)
            just_left = key_vector(center, boundary - epsilon, points, resolutions)
            just_right = key_vector(center, boundary + epsilon, points, resolutions)
            assert boundary in representatives
            if at_boundary != just_left and at_boundary != just_right:
                genuinely_new_boundary_vectors += 1
            for point, resolution in zip(points, resolutions):
                position = center + boundary * point
                if (resolution * position).denominator == 1:
                    sign = 1 if point > 0 else -1
                    at_key = periodic_key(position, resolution)
                    assert at_key == periodic_key(center + (boundary + sign * epsilon) * point, resolution)
                    assert at_key != periodic_key(center + (boundary - sign * epsilon) * point, resolution)
                    orientation_checks += 1
    assert genuinely_new_boundary_vectors > 0
    return {
        "centers": len(centers),
        "signed_orientation_checks": orientation_checks,
        "boundary_vectors_different_from_both_one_sided_vectors": genuinely_new_boundary_vectors,
        "significance": "Sampling only open scale intervals misses these boundary vectors.",
        "passed": True,
    }


def recurrence_terms(coefficients, initial, count: int):
    values = list(initial)
    order = len(coefficients)
    assert len(initial) == order
    while len(values) < count:
        values.append(sum(coefficients[i] * values[-order + i] for i in range(order)))
    return values


def verify_signed_first_crossings() -> dict:
    cases = [
        {
            "label": "nonreal_roots_with_exact_zeros",
            "coefficients": [Fraction(-1, 4), Fraction(0)],
            "initial": [Fraction(1), Fraction(0)],
            "alpha": Fraction(1, 4),
            "Q": Fraction(1, 32),
        },
        {
            "label": "nonreal_roots_with_maximum_ties",
            "coefficients": [Fraction(-1, 4), Fraction(0)],
            "initial": [Fraction(1), Fraction(1)],
            "alpha": Fraction(1, 4),
            "Q": Fraction(1, 32),
        },
        {
            "label": "repeated_root_one_half",
            "coefficients": [Fraction(-1, 4), Fraction(1)],
            "initial": [Fraction(1), Fraction(1)],
            "alpha": Fraction(1, 2),
            "Q": Fraction(1, 16),
        },
    ]
    levels = 7
    reports = []
    for case in cases:
        alpha = case["alpha"]
        q = case["Q"]
        beta = Fraction(3, 4)
        constant = Fraction(2)
        order = len(case["coefficients"])
        assert 0 < q < alpha / 4
        crossing_multiplier = 1
        while beta**crossing_multiplier > q / constant:
            crossing_multiplier += 1
        count = crossing_multiplier * levels + order
        values = recurrence_terms(case["coefficients"], case["initial"], count)
        block_norms = [max(abs(value) for value in values[n : n + order]) for n in range(count - order + 1)]
        assert block_norms[0] == 1
        for n in range(len(block_norms) - 1):
            assert block_norms[n + 1] >= alpha * block_norms[n]
            assert block_norms[n] <= constant * beta**n
        selected = []
        selected_indices = []
        crossings = []
        tie_count = 0
        for level in range(1, levels + 1):
            crossing = next(n for n in range(1, len(block_norms)) if block_norms[n] <= q**level)
            assert crossing <= crossing_multiplier * level
            assert all(block_norms[n] > q**level for n in range(crossing))
            maximizing = [i for i in range(order) if abs(values[crossing + i]) == block_norms[crossing]]
            chosen = min(maximizing)
            tie_count += int(len(maximizing) > 1)
            scalar = values[crossing + chosen]
            assert alpha * q**level < abs(scalar) <= q**level
            assert scalar != 0
            selected.append(scalar)
            selected_indices.append(crossing + chosen)
            crossings.append({"level": level, "first_crossing": crossing, "chosen_coordinate": chosen})
        assert len(set(selected_indices)) == levels
        for j in range(levels):
            for k in range(j + 1, levels):
                assert abs(selected[j] - selected[k]) > (alpha - q) * q ** (j + 1)
        if case["label"] == "nonreal_roots_with_exact_zeros":
            assert any(value == 0 for value in values)
            assert any(value > 0 for value in selected) and any(value < 0 for value in selected)
        if case["label"] == "nonreal_roots_with_maximum_ties":
            assert tie_count == levels
        reports.append({
            "label": case["label"],
            "coefficients": [rational_string(value) for value in case["coefficients"]],
            "initial_state": [rational_string(value) for value in case["initial"]],
            "terms_checked": len(values),
            "selected_indices": selected_indices,
            "selected_signs": [1 if value > 0 else -1 for value in selected],
            "maximizer_ties_resolved": tie_count,
            "crossings": crossings,
        })
    return {"exact_rational_cases": reports, "passed": True}


def verify_separation_and_stability() -> dict:
    mu = Fraction(2, 3)
    c = 4 / (1 - mu)
    ratios = [Fraction(1, 3), Fraction(1, 2), Fraction(2, 3)]
    points = [Fraction(1, 8)]
    for index in range(9):
        points.append(points[-1] * ratios[index % len(ratios)])
    centers = [Fraction(0), Fraction(1, 7), Fraction(127, 128)]
    separation_cases = 0
    for start in range(4):
        for length in range(1, 5):
            window = points[start : start + length]
            resolution = 1
            while resolution < c / window[-1]:
                resolution *= 2
            assert c / window[-1] <= resolution < 2 * c / window[-1]
            for center in centers:
                _, representatives = boundary_representatives(center, window, [resolution] * length)
                for t in representatives:
                    for refinement in (1, 2, 4):
                        keys = [periodic_key(center, refinement * resolution)]
                        keys.extend(periodic_key(center + t * a, refinement * resolution) for a in window)
                        assert len(set(keys)) == len(keys)
                        separation_cases += 1

    # Exact stability test for one earlier grid.  The bad intervals are
    # [gamma-2a, gamma), including their left endpoints but not gamma itself.
    earlier_resolution = 64
    first_later_point = Fraction(1, 1024)
    bad_density = 2 * earlier_resolution * first_later_point
    assert bad_density == Fraction(1, 8)
    stable_centers = 0
    unstable_centers = 0
    for integer in range(4096):
        center = Fraction(integer, 4096)
        cell_index = floor_fraction(earlier_resolution * center)
        next_boundary = Fraction(cell_index + 1, earlier_resolution)
        stable = center + 2 * first_later_point < next_boundary
        if stable:
            stable_centers += 1
            for point in (first_later_point, first_later_point / 2, first_later_point / 3):
                for t in (Fraction(1), Fraction(3, 2), Fraction(2)):
                    assert periodic_key(center + t * point, earlier_resolution) == periodic_key(center, earlier_resolution)
        else:
            unstable_centers += 1
            assert periodic_key(center + 2 * first_later_point, earlier_resolution) != periodic_key(center, earlier_resolution)
    assert Fraction(unstable_centers, 4096) == bad_density
    return {
        "exact_distinct_key_checks_across_three_refinements": separation_cases,
        "stability_mesh_size": 4096,
        "stable_centers": stable_centers,
        "unstable_centers": unstable_centers,
        "exact_instability_density": rational_string(bad_density),
        "passed": True,
    }


def preorder_paths(branching: int, depth: int, prefix=()):
    if depth == 0:
        return
    for child in range(branching):
        path = prefix + (child,)
        yield path
        yield from preorder_paths(branching, depth - 1, path)


def verify_window_spans() -> dict:
    parameter_cases = 0
    edge_cases = 0
    for branching in range(2, 5):
        for depth in range(1, 5):
            for gap in range(1, 4):
                for base_length in range(1, 5):
                    parameter_cases += 1
                    lengths = {1: base_length}
                    spans = {1: branching * base_length + (branching - 1) * gap}
                    for height in range(2, depth + 1):
                        lengths[height] = max(base_length, gap + spans[height - 1])
                        spans[height] = (
                            branching * (lengths[height] + gap + spans[height - 1])
                            + (branching - 1) * gap
                        )
                    cursor = 7
                    concrete = []
                    for path in preorder_paths(branching, depth):
                        height = depth - len(path) + 1
                        last = cursor + lengths[height] - 1
                        concrete.append((path, height, cursor, last))
                        cursor = last + gap + 1
                    assert len(concrete) == sum(branching**height for height in range(1, depth + 1))
                    assert concrete[-1][3] - concrete[0][2] + 1 == spans[depth]
                    for index, (path, height, first, last) in enumerate(concrete):
                        descendant_end = last
                        next_index = index + 1
                        while next_index < len(concrete):
                            next_path, _, _, next_last = concrete[next_index]
                            if next_path[: len(path)] != path:
                                break
                            descendant_end = next_last
                            next_index += 1
                        assert descendant_end - first + 1 <= 2 * lengths[height]
                        edge_cases += 1
                    growth = 2 * branching
                    geometric_sum = (growth ** (depth - 1) - 1) // (growth - 1)
                    assert geometric_sum * (growth - 1) == growth ** (depth - 1) - 1
                    closed_span = (
                        growth ** (depth - 1) * spans[1]
                        + (3 * branching - 1) * gap * geometric_sum
                    )
                    assert closed_span == spans[depth]
                    assert closed_span <= (base_length + gap) * growth**depth
    return {
        "parameter_combinations": parameter_cases,
        "individual_edge_and_subtree_checks": edge_cases,
        "branching_range": [2, 4],
        "depth_range": [1, 4],
        "gap_range": [1, 3],
        "base_window_range": [1, 4],
        "passed": True,
    }


def log_add_exp(left: float, right: float) -> float:
    larger = max(left, right)
    return larger + math.log1p(math.exp(-abs(left - right)))


def logarithmic_budget_row(label: str, loglog_n: float, max_gap: float, expect_success: bool) -> dict:
    """Floating-point sanity checks of analytic bounds, with very wide margins.

    The astronomical N, d, K and tree are never constructed.  loglog_n encodes
    log(log(N)).  All assertions here are checks of the displayed *bounds*, not
    rigorous interval arithmetic certificates or approximations to the set K.
    """
    p = 1 / 20
    mu = 1 / 2
    c = 4 / (1 - mu)
    branching = math.floor(loglog_n / (2 * math.log(2)))
    alpha = p * (branching - 1) / 2
    beta = alpha - 2 * max_gap
    log_uniform_failure_bound = math.log((6 + 4 * c) * branching) - beta
    entropy_success = beta >= 1 and log_uniform_failure_bound < math.log(p)

    # d = ceil(2^(M-1) log(2/p)) <= 2^(M-1) (log(2/p)+1).
    log_depth_upper = (branching - 1) * math.log(2) + math.log(math.log(2 / p) + 1)
    contraction_log = math.log(1 / mu)
    # g = ceil((log(16c/p) + d log M)/log(1/mu)); use its upper bound.
    log_gap_plus_one_upper = log_add_exp(
        math.log(math.log(16 * c / p) + 2 * contraction_log),
        log_depth_upper + math.log(math.log(branching)),
    ) - math.log(contraction_log)
    # sigma_d <= (g+1)(2M)^d, so compare log(log(sigma_d)) with loglog N.
    log_log_span_upper = log_add_exp(
        log_depth_upper + math.log(math.log(2 * branching)),
        math.log(log_gap_plus_one_upper),
    )
    # This stronger inequality proves sigma_d <= sqrt(N); a fixed starting
    # index is consequently harmless for sufficiently large N.
    prefix_fits = log_log_span_upper < loglog_n - math.log(2)
    actual_success = entropy_success and prefix_fits
    assert actual_success == expect_success
    return {
        "label": label,
        "log_log_N": loglog_n,
        "max_logarithmic_gap": max_gap,
        "p": p,
        "mu": mu,
        "branching": branching,
        "beta": beta,
        "log_uniform_miss_bound_when_beta_ge_1": log_uniform_failure_bound if beta >= 1 else None,
        "log_p": math.log(p),
        "log_log_span_upper": log_log_span_upper,
        "log_log_sqrt_N": loglog_n - math.log(2),
        "prefix_fits": prefix_fits,
        "entropy_condition_succeeds": entropy_success,
        "expected_outcome": "success" if expect_success else "failure_of_this_parameter_choice",
        "passed": True,
    }


def verify_logarithmic_budgets() -> dict:
    cases = [
        ("bounded_gap_success", 1_000.0, 1.0, True),
        ("sqrt_loglog_insufficient_budget", 10_000.0, 100.0, False),
        ("sqrt_loglog_large_budget_success", 1_000_000.0, 1_000.0, True),
        ("proportional_loglog_gap_negative_control", 1_000_000.0, 10_000.0, False),
    ]
    return {
        "qualification": "Floating-point sanity checks of analytic upper bounds; no astronomical tree is generated.",
        "rows": [logarithmic_budget_row(*case) for case in cases],
        "passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="Also save the JSON report to this path.")
    args = parser.parse_args()
    report = {
        "scope": "Finite independent checks corroborate proof lemmas; they do not prove the infinite theorem or certify novelty.",
        "conditional_independence": verify_conditioning(),
        "dilation_boundaries": verify_boundary_representatives(),
        "signed_dilation_boundaries": verify_signed_boundaries(),
        "signed_first_crossings": verify_signed_first_crossings(),
        "grid_separation_and_stability": verify_separation_and_stability(),
        "integer_window_spans": verify_window_spans(),
        "logarithmic_budgets": verify_logarithmic_budgets(),
        "all_checks_passed": True,
    }
    output = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
