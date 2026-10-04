#!/usr/bin/env python3
"""Exact finite checks for blind-output games and success-law polytopes.

Run ``python3 verify_finite.py``.  All arithmetic is integral or rational;
there is no sampling and there are no third-party dependencies.  The output
is deterministic JSON.  These checks do not prove an infinite measure
extension theorem and make no claim about historical novelty.
"""

from __future__ import annotations

from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product
import json
from math import comb, lcm


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def bits(value, length):
    """Coordinates are printed left-to-right; coordinate zero is leftmost."""
    return tuple((value >> (length - 1 - i)) & 1 for i in range(length))


def bit_string(pattern):
    return "".join(map(str, pattern))


def perfect_matchings(n):
    """Generate each perfect matching of the binary n-cube once."""
    vertex_count = 1 << n

    def visit(remaining, edges):
        if not remaining:
            yield tuple(edges)
            return
        first = min(remaining)
        for coordinate in range(n):
            second = first ^ (1 << (n - 1 - coordinate))
            if second in remaining:
                yield from visit(
                    remaining - {first, second},
                    edges + [(first, second, coordinate)],
                )

    yield from visit(frozenset(range(vertex_count)), [])


def blind_maps(n):
    """Edge labels are guesses; endpoints have the same selected output."""
    result = []
    matchings = list(perfect_matchings(n))
    for matching in matchings:
        for labels in product((0, 1), repeat=len(matching)):
            outputs = [None] * (1 << n)
            for (left, right, coordinate), guess in zip(matching, labels):
                outputs[left] = outputs[right] = (coordinate, guess)
            result.append(tuple(outputs))
    require(len(result) == len(set(result)), "Duplicate blind map")
    return matchings, result


def success_vector(outputs, n):
    result = []
    for vertex, (coordinate, guess) in enumerate(outputs):
        neighbor = vertex ^ (1 << (n - 1 - coordinate))
        require(outputs[neighbor] == (coordinate, guess), "Blindness failed")
        result.append(int(bits(vertex, n)[coordinate] == guess))
    return tuple(result)


def check_cubes():
    summaries = []
    n2_maps = None
    n2_scores = None
    for n, expected_matchings, expected_maps in [(1, 1, 2), (2, 2, 8), (3, 9, 144)]:
        matchings, maps = blind_maps(n)
        vectors = [success_vector(outputs, n) for outputs in maps]
        require(len(matchings) == expected_matchings, "Wrong matching count")
        require(len(maps) == expected_maps, "Wrong blind-map count")
        require(all(sum(s) == 1 << (n - 1) for s in vectors), "Fairness failed")
        summaries.append({
            "coordinates": n,
            "configurations": 1 << n,
            "perfect_matchings": len(matchings),
            "blind_maps": len(maps),
            "successes_per_map": 1 << (n - 1),
            "uniform_success_probability": "1/2",
        })
        if n == 2:
            n2_maps, n2_scores = maps, vectors

    histogram = Counter()
    attaining = None
    for team in product(range(len(n2_maps)), repeat=3):
        scores = tuple(sum(n2_scores[p][x] for p in team) for x in range(4))
        guaranteed = min(scores)
        histogram[guaranteed] += 1
        require(guaranteed <= 1, "A triple exceeds floor(3/2)")
        if guaranteed == 1 and attaining is None:
            attaining = (team, scores)
    require(sum(histogram.values()) == 512, "Not all ordered triples checked")
    require(attaining is not None, "No attaining triple")
    team, scores = attaining
    witness = []
    for vertex in range(4):
        witness.append({
            "configuration": bit_string(bits(vertex, 2)),
            "player_outputs": [list(n2_maps[p][vertex]) for p in team],
            "correct_players": scores[vertex],
        })
    return {
        "individual_maps": summaries,
        "ordered_three_player_teams_on_two_coordinates": {
            "teams_checked": 512,
            "guaranteed_score_histogram": {str(k): histogram[k] for k in sorted(histogram)},
            "optimal_guaranteed_score": max(histogram),
            "attaining_witness": witness,
        },
    }


def feasible_patterns(targets, guesses, alphabet_size, internal_values=None):
    """Enumerate algebraic patterns for fixed internal and free external values."""
    require(len(targets) == len(guesses), "Output arrays have different lengths")
    internal_values = dict(internal_values or {})
    external = tuple(dict.fromkeys(t for t in targets if t not in internal_values))
    patterns = set()
    for values in product(range(alphabet_size), repeat=len(external)):
        assignment = internal_values | dict(zip(external, values))
        patterns.add(tuple(int(assignment[t] == a) for t, a in zip(targets, guesses)))
    return tuple(sorted(patterns))


def check_patterns():
    cases = [
        ("shared_binary_target_guesses_001", ("z", "z", "z"), (0, 0, 1), 2,
         {}, {"001", "110"}),
        ("three_distinct_binary_targets", ("x", "y", "z"), (0, 0, 1), 2,
         {}, {bit_string(p) for p in product((0, 1), repeat=3)}),
        ("shared_ternary_target_guesses_001", ("z", "z", "z"), (0, 0, 1), 3,
         {}, {"000", "001", "110"}),
        ("one_internal_success_and_shared_opposite_guesses", ("k", "z", "z"),
         (1, 0, 1), 2, {"k": 1}, {"101", "110"}),
        ("two_external_collision_groups", ("x", "x", "y", "y"), (0, 1, 0, 0), 2,
         {}, {"0100", "0111", "1000", "1011"}),
    ]
    result = []
    for name, targets, guesses, q, internal, expected in cases:
        actual = {bit_string(p) for p in feasible_patterns(targets, guesses, q, internal)}
        require(actual == expected, "Unexpected feasible patterns in " + name)
        result.append({"case": name, "alphabet_size": q, "patterns": sorted(actual)})
    return result


def dot(left, right):
    return sum((a * b for a, b in zip(left, right)), Fraction(0))


def solve_square(matrix, right):
    """Exact Gaussian elimination; return None for singular systems."""
    n = len(right)
    rows = [[Fraction(a) for a in row] + [Fraction(b)] for row, b in zip(matrix, right)]
    for column in range(n):
        pivot = next((r for r in range(column, n) if rows[r][column]), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [entry / scale for entry in rows[column]]
        for r in range(n):
            if r != column and rows[r][column]:
                scale = rows[r][column]
                rows[r] = [a - scale * b for a, b in zip(rows[r], rows[column])]
    return tuple(row[-1] for row in rows)


def hall_inequalities(pattern_count, weighted_sets):
    """Return A p <= b, including nonnegativity and every subset Hall bound."""
    inequalities = set()
    for i in range(pattern_count):
        row = tuple(-int(j == i) for j in range(pattern_count))
        inequalities.add((row, Fraction(0)))
    for mask in range(1 << pattern_count):
        subset = {i for i in range(pattern_count) if mask & (1 << i)}
        row = tuple(int(i in subset) for i in range(pattern_count))
        bound = sum((weight for choices, weight in weighted_sets if subset.intersection(choices)), Fraction(0))
        inequalities.add((row, bound))
    return tuple(sorted(inequalities))


def satisfies_hall(point, inequalities):
    return sum(point) == 1 and all(dot(row, point) <= bound for row, bound in inequalities)


def hall_vertices(pattern_count, inequalities):
    """A bounded polytope vertex has enough independent active constraints."""
    vertices = set()
    for active in combinations(inequalities, pattern_count - 1):
        matrix = [(1,) * pattern_count] + [row for row, _ in active]
        right = [Fraction(1)] + [bound for _, bound in active]
        point = solve_square(matrix, right)
        if point is not None and satisfies_hall(point, inequalities):
            vertices.add(point)
    return vertices


def weighted_selection_points(pattern_count, weighted_sets):
    """The Minkowski sum is the convex hull of these vertex-selection sums."""
    points = set()
    for selected in product(*(choices for choices, _ in weighted_sets)):
        point = [Fraction(0)] * pattern_count
        for index, (_, weight) in zip(selected, weighted_sets):
            point[index] += weight
        points.add(tuple(point))
    return points


def transport_feasible(point, weighted_sets):
    """Independent exact membership test by integer max flow after rescaling."""
    scale = lcm(*(x.denominator for x in point), *(w.denominator for _, w in weighted_sets))
    type_count, pattern_count = len(weighted_sets), len(point)
    source, sink = 0, 1 + type_count + pattern_count
    capacities = [[0] * (sink + 1) for _ in range(sink + 1)]
    for i, (choices, weight) in enumerate(weighted_sets, 1):
        capacities[source][i] = int(weight * scale)
        for j in choices:
            capacities[i][1 + type_count + j] = scale
    for j, mass in enumerate(point):
        capacities[1 + type_count + j][sink] = int(mass * scale)

    flow = 0
    while True:
        previous = [-1] * (sink + 1)
        previous[source] = source
        queue = deque([source])
        while queue and previous[sink] == -1:
            vertex = queue.popleft()
            for neighbor, capacity in enumerate(capacities[vertex]):
                if capacity > 0 and previous[neighbor] == -1:
                    previous[neighbor] = vertex
                    queue.append(neighbor)
        if previous[sink] == -1:
            return flow == scale
        amount = scale
        vertex = sink
        while vertex != source:
            amount = min(amount, capacities[previous[vertex]][vertex])
            vertex = previous[vertex]
        vertex = sink
        while vertex != source:
            parent = previous[vertex]
            capacities[parent][vertex] -= amount
            capacities[vertex][parent] += amount
            vertex = parent
        flow += amount


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in compositions(total - first, length - 1):
                yield (first,) + tail


def check_polytope(name, labels, weighted_sets, lattice_denominator=None):
    weighted_sets = tuple((tuple(sorted(choices)), Fraction(weight)) for choices, weight in weighted_sets)
    require(all(choices and weight >= 0 for choices, weight in weighted_sets), "Invalid weighted sets")
    require(sum(w for _, w in weighted_sets) == 1, "Weights do not sum to one")
    count = len(labels)
    inequalities = hall_inequalities(count, weighted_sets)
    selections = weighted_selection_points(count, weighted_sets)
    vertices = hall_vertices(count, inequalities)
    require(vertices, "Empty Hall polytope")
    require(all(satisfies_hall(p, inequalities) for p in selections), "Selection violates Hall")
    require(vertices <= selections, "Hall vertex absent from Minkowski selection sums")
    # Thus conv(selections) <= Hall polytope <= conv(vertices) <= conv(selections).

    result = {
        "case": name,
        "pattern_order": list(labels),
        "weighted_feasible_sets": [
            {"patterns": [labels[i] for i in choices], "weight": str(weight)}
            for choices, weight in weighted_sets
        ],
        "distinct_vertex_selection_sums": len(selections),
        "hall_polytope_vertices": [[str(x) for x in p] for p in sorted(vertices)],
        "exact_polytope_equality_verified": True,
    }
    if lattice_denominator is not None:
        feasible_count = 0
        tested_count = 0
        for integer_point in compositions(lattice_denominator, count):
            point = tuple(Fraction(x, lattice_denominator) for x in integer_point)
            hall = satisfies_hall(point, inequalities)
            flow = transport_feasible(point, weighted_sets)
            require(hall == flow, "Hall and exact max-flow disagree")
            feasible_count += int(hall)
            tested_count += 1
        require(tested_count == comb(lattice_denominator + count - 1, count - 1), "Missing lattice points")
        result["independent_lattice_flow_check"] = {
            "denominator": lattice_denominator,
            "points_checked": tested_count,
            "feasible_points": feasible_count,
        }
    return result


def check_mixed_polytopes():
    labels = ("00", "01", "10", "11")
    return [
        check_polytope(
            "same_guesses_opposite_guesses_and_distinct_targets", labels,
            [((0, 3), Fraction(1, 2)), ((1, 2), Fraction(1, 3)),
             ((0, 1, 2, 3), Fraction(1, 6))], 12,
        ),
        check_polytope(
            "fixed_pattern_and_two_internal_external_cells", labels,
            [((0,), Fraction(1, 4)), ((1, 3), Fraction(1, 4)),
             ((2, 3), Fraction(1, 2))], 8,
        ),
    ]


def check_atomic_intervals():
    result = []
    for q in (2, 3, 5):
        for alpha in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(1)):
            weighted_sets = [((0,), alpha * (q - 1) / q),
                             ((1,), alpha / q), ((0, 1), 1 - alpha)]
            checked = check_polytope("single_player", ("0", "1"), weighted_sets)
            endpoints = sorted(Fraction(p[1]) for p in checked["hall_polytope_vertices"])
            lower, upper = alpha / q, 1 - (q - 1) * alpha / q
            require(endpoints == sorted({lower, upper}), "Atomic interval formula failed")
            result.append({"alphabet_size": q, "atomic_mass": str(alpha),
                           "minimum_success": str(lower), "maximum_success": str(upper)})
    return result


def main():
    result = {
        "status": "all_exact_checks_passed",
        "scope": (
            "Finite exhaustive combinatorics and rational polytope checks only; "
            "no simulation, no verification of an infinite measure-extension proof, "
            "and no historical-novelty claim."
        ),
        "binary_cube_games": check_cubes(),
        "collision_feasibility": check_patterns(),
        "mixed_joint_law_polytopes": check_mixed_polytopes(),
        "single_player_atomic_interval_specializations": check_atomic_intervals(),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
