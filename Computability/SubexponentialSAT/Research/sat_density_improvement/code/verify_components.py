#!/usr/bin/env python3
"""Exact finite checks for a density-sensitive counting-algorithm proposal.

This is NOT an implementation of the subexponential counting algorithm and
does not verify the external tensor-contraction or expander theorems.
It checks independently reproducible, finite components of the proposed
reduction using only Python's standard library. All assertions relevant to
correctness use integers or fractions.Fraction; no floating point is used.

Run:
    python3 verify_components.py
    python3 verify_components.py --output verification_results.json

The JSON report records the tested ranges and explicitly distinguishes
finite verification from a proof for arbitrary input sizes.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from math import comb, isqrt
from pathlib import Path
import platform
import time


INVERSE_PORT = (1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15)


def lazy_mgg_neighbor(side_length: int, vertex: int, port: int) -> int:
    """The eight Margulis--Gabber--Galil maps, followed by eight loops.

    Vertices are (x,y) in (Z/side_length Z)^2, encoded as x*side_length+y.
    Ports remain distinct even when their endpoints coincide.
    """
    if side_length < 1 or not (0 <= vertex < side_length**2):
        raise ValueError("invalid graph size or vertex")
    if not 0 <= port < 16:
        raise ValueError("port must be in 0..15")
    x, y = divmod(vertex, side_length)
    if port == 0:
        x += 2 * y
    elif port == 1:
        x -= 2 * y
    elif port == 2:
        x += 2 * y + 1
    elif port == 3:
        x -= 2 * y + 1
    elif port == 4:
        y += 2 * x
    elif port == 5:
        y -= 2 * x
    elif port == 6:
        y += 2 * x + 1
    elif port == 7:
        y -= 2 * x + 1
    return (x % side_length) * side_length + y % side_length


def lazy_mgg_adjacency(side_length: int) -> list[list[int]]:
    size = side_length**2
    adjacency = [[0] * size for _ in range(size)]
    for vertex in range(size):
        for port in range(16):
            adjacency[vertex][lazy_mgg_neighbor(side_length, vertex, port)] += 1
    return adjacency


def check_graph_ports() -> dict:
    records = []
    port_checks = 0
    for side_length in range(2, 9):
        size = side_length**2
        adjacency = lazy_mgg_adjacency(side_length)
        for vertex in range(size):
            assert sum(adjacency[vertex]) == 16
            for neighbor in range(size):
                assert adjacency[vertex][neighbor] == adjacency[neighbor][vertex]
            for port in range(16):
                neighbor = lazy_mgg_neighbor(side_length, vertex, port)
                assert lazy_mgg_neighbor(side_length, neighbor, INVERSE_PORT[port]) == vertex
                port_checks += 1
        for port in range(16):
            assert len({lazy_mgg_neighbor(side_length, v, port) for v in range(size)}) == size
        records.append({"side_length": side_length, "vertices": size, "degree": 16})
    return {
        "status": "passed",
        "claim_checked": "finite symmetry, degree, inverse-port, and permutation identities",
        "port_inversion_checks": port_checks,
        "graphs": records,
    }


def positive_ldl_pivots(matrix: list[list[int]]) -> list[Fraction]:
    """Exact symmetric Schur elimination; positive pivots certify SPD.

    No pivoting is needed when the matrix is positive definite. This
    routine raises if a nonpositive pivot is encountered.
    """
    size = len(matrix)
    work = [[Fraction(value) for value in row] for row in matrix]
    assert all(len(row) == size for row in work)
    assert all(work[i][j] == work[j][i] for i in range(size) for j in range(size))
    pivots = []
    for index in range(size):
        pivot = work[index][index]
        assert pivot > 0, (index, pivot)
        pivots.append(pivot)
        for row in range(index + 1, size):
            for column in range(row, size):
                value = work[row][column] - work[row][index] * work[index][column] / pivot
                work[row][column] = value
                work[column][row] = value
    return pivots


def check_finite_spectral_certificates() -> dict:
    records = []
    for side_length in range(2, 6):
        adjacency = lazy_mgg_adjacency(side_length)
        size = side_length**2
        last = size - 1
        # Columns of B are e_i-e_last. Thus B spans the constants-orthogonal
        # subspace. The integer matrix below is
        # 80 B^T[(19/20)I - A/16]B.
        certificate = []
        for row in range(last):
            values = []
            for column in range(last):
                gram = 2 if row == column else 1
                compressed = (
                    adjacency[row][column]
                    - adjacency[row][last]
                    - adjacency[last][column]
                    + adjacency[last][last]
                )
                values.append(76 * gram - 5 * compressed)
            certificate.append(values)
        pivots = positive_ldl_pivots(certificate)
        records.append({
            "side_length": side_length,
            "vertices": size,
            "certificate_dimension": last,
            "positive_exact_pivots": len(pivots),
            "smallest_pivot": str(min(pivots)),
            "all_pivots": [str(value) for value in pivots],
        })
    # Given the external 5 sqrt(2)/8 bound for the nonlazy graph,
    # this exact inequality establishes (1+5 sqrt(2)/8)/2 < 19/20.
    assert 50 * 100 < 81 * 64
    return {
        "status": "passed",
        "claim_checked": "finite exact upper spectral certificates on the constants-orthogonal subspace",
        "limitation": "these four finite certificates do not prove the expander theorem for all sizes",
        "bound": "19/20",
        "certificates": records,
    }


def kernel_words(rows: tuple[int, ...], length: int) -> list[int]:
    return [word for word in range(1 << length)
            if all((row & word).bit_count() % 2 == 0 for row in rows)]


def minimum_distance(words: list[int]) -> int | None:
    nonzero = [word.bit_count() for word in words if word]
    return min(nonzero) if nonzero else None


def find_small_local_code(length: int, row_count: int, target_distance: int) -> tuple:
    """Exhaustively search binary parity-check matrices in a fixed order."""
    trials = 0
    for rows in product(range(1 << length), repeat=row_count):
        trials += 1
        words = kernel_words(rows, length)
        distance = minimum_distance(words)
        if distance is None or distance >= target_distance:
            return rows, words, distance, trials
    raise AssertionError("toy code search unexpectedly had no solution")


def repetition_tanner_rows(edges: list[tuple[int, int]]) -> tuple[int, ...]:
    """Enforce repetition at each endpoint, preserving all edge identities.

    Edge list positions are distinct ports, including parallel edges.
    For each incident-edge list, equate its first bit to every other bit.
    """
    rows = []
    for endpoint in (0, 1):
        for vertex in sorted({edge[endpoint] for edge in edges}):
            incident = [index for index, edge in enumerate(edges) if edge[endpoint] == vertex]
            for index in incident[1:]:
                rows.append((1 << incident[0]) | (1 << index))
    return tuple(rows)


def zero_fill(word: int, retained: tuple[int, ...]) -> int:
    lifted = 0
    for new_index, old_index in enumerate(retained):
        if (word >> new_index) & 1:
            lifted |= 1 << old_index
    return lifted


def shorten_rows(rows: tuple[int, ...], retained: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sum(((row >> old_index) & 1) << new_index
                     for new_index, old_index in enumerate(retained))
                 for row in rows)


def check_codes_and_shortening() -> dict:
    local_records = []
    for length, row_count, target in ((2, 1, 2), (3, 2, 3), (4, 3, 4), (5, 3, 3), (6, 3, 3)):
        rows, words, distance, trials = find_small_local_code(length, row_count, target)
        assert distance is not None and distance >= target
        local_records.append({
            "length": length, "rows": row_count, "target_distance": target,
            "actual_distance": distance, "kernel_size": len(words),
            "matrices_examined": trials, "check_rows_as_bitmasks": list(rows),
        })

    k22 = [(left, right) for left in range(2) for right in range(2)]
    two_k22 = k22 + [(left + 2, right + 2) for left, right in k22]
    toy_examples = [
        ("one pair with two parallel edges", [(0, 0), (0, 0)], (0, 1)),
        ("complete bipartite K2,2", k22, (0, 1, 2, 3)),
        ("two parallel-edge components, shortened", [(0, 0), (0, 0), (1, 1), (1, 1)], (0, 1, 2)),
        ("two K2,2 components, shortened", two_k22, tuple(range(7))),
    ]
    tanner_records = []
    lift_checks = 0
    for name, edges, retained in toy_examples:
        rows = repetition_tanner_rows(edges)
        original = kernel_words(rows, len(edges))
        shortened = kernel_words(shorten_rows(rows, retained), len(retained))
        expected = []
        for word in range(1 << len(retained)):
            lifted = zero_fill(word, retained)
            assert bool(word in shortened) == bool(lifted in original)
            assert lifted.bit_count() == word.bit_count()
            for index in range(len(edges)):
                if index not in retained:
                    assert ((lifted >> index) & 1) == 0
            if lifted in original:
                expected.append(word)
            lift_checks += 1
        assert expected == shortened
        assert len({zero_fill(word, retained) for word in shortened}) == len(shortened)
        original_distance = minimum_distance(original)
        shortened_distance = minimum_distance(shortened)
        assert shortened_distance is None or shortened_distance >= original_distance
        tanner_records.append({
            "example": name, "original_edges": len(edges), "retained_edges": len(retained),
            "original_kernel_size": len(original), "shortened_kernel_size": len(shortened),
            "original_minimum_distance": original_distance,
            "shortened_minimum_distance": shortened_distance,
            "unique_lift_kind": "zero extension to discarded edge coordinates",
        })
    return {
        "status": "passed", "local_codes": local_records,
        "tanner_examples": tanner_records, "zero_extension_checks": lift_checks,
        "limitation": "small toy codes and graphs; no claim to instantiate the enormous asymptotic parameters",
    }


def rank_subset(length: int, subset: tuple[int, ...]) -> int:
    """Rank a fixed-size subset in ordinary lexicographic order."""
    if tuple(sorted(set(subset))) != subset or any(x < 0 or x >= length for x in subset):
        raise ValueError("invalid subset")
    rank = 0
    start = 0
    remaining = len(subset)
    for chosen in subset:
        for candidate in range(start, chosen):
            rank += comb(length - candidate - 1, remaining - 1)
        start = chosen + 1
        remaining -= 1
    return rank


def unrank_subset(length: int, cardinality: int, rank: int) -> tuple[int, ...]:
    if not 0 <= cardinality <= length or not 0 <= rank < comb(length, cardinality):
        raise ValueError("invalid subset rank")
    result = []
    start = 0
    remaining = cardinality
    while remaining:
        for candidate in range(start, length - remaining + 1):
            block = comb(length - candidate - 1, remaining - 1)
            if rank < block:
                result.append(candidate)
                start = candidate + 1
                remaining -= 1
                break
            rank -= block
        else:
            raise AssertionError("unranking exhausted its search")
    return tuple(result)


def ceil_log2_integer(value: int) -> int:
    if value < 1:
        raise ValueError("positive integer required")
    return (value - 1).bit_length()


def check_subset_encoding() -> dict:
    subset_checks = 0
    for length in range(11):
        for cardinality in range(length + 1):
            for rank, subset in enumerate(combinations(range(length), cardinality)):
                assert rank_subset(length, subset) == rank
                assert unrank_subset(length, cardinality, rank) == subset
                subset_checks += 1
    wire_checks = 0
    for capacities in product(range(4), repeat=4):
        total_capacity = sum(capacities)
        for degrees in product(*(range(capacity + 1) for capacity in capacities)):
            choices = [comb(capacity, degree) for capacity, degree in zip(capacities, degrees)]
            choice_product = 1
            for value in choices:
                choice_product *= value
            wires = sum(ceil_log2_integer(value) for value in choices)
            # Exact exponentiated form of M <= (#cells)+log_2(product choices).
            assert (1 << wires) <= (1 << len(capacities)) * choice_product
            for extra_budget in range(3):
                budget = sum(degrees) + extra_budget
                stars_and_bars = comb(total_capacity + budget, budget)
                assert choice_product <= stars_and_bars
                assert wires <= len(capacities) + ceil_log2_integer(stars_and_bars)
                if budget:
                    # The usual entropy estimate with the safe rational
                    # replacement e<3, checked without logarithms or floats.
                    assert stars_and_bars * budget**budget <= (3 * (total_capacity + budget))**budget
                wire_checks += 1
    return {
        "status": "passed", "subset_length_range": [0, 10],
        "rank_unrank_checks": subset_checks,
        "wire_entropy_checks": wire_checks,
        "grid": "all 2-by-2 capacity arrays with each cell in 0..3, all feasible degree arrays, three total budgets",
        "arithmetic": "exact integers, binomial coefficients, and exponentiated inequalities",
    }


def parity_candidate_rows(length: int, samples: int) -> list[int]:
    alphabet = tuple((coordinate, coefficient) for coordinate in range(length) for coefficient in (0, 1))
    rows = []
    for candidate in product(alphabet, repeat=samples):
        row = 0
        for coordinate, coefficient in candidate:
            if coefficient:
                row ^= 1 << coordinate
        rows.append(row)
    return rows


def check_greedy_parity() -> dict:
    examples = []
    rounds_checked = 0
    for length, samples, assignment_bits, variant in (
        (4, 2, 3, "all_even_words"),
        (4, 2, 5, "repeated_words"),
        (4, 2, 3, "only_zero"),
        (4, 2, 4, "no_zero"),
        (5, 3, 4, "all_even_words"),
        (6, 3, 5, "all_even_words"),
    ):
        accepted_code = [word for word in range(1 << length) if word.bit_count() % 2 == 0]
        assert all(samples * word.bit_count() >= length for word in accepted_code if word)
        assignment_count = 1 << assignment_bits
        if variant == "all_even_words":
            violations = [accepted_code[x % len(accepted_code)] for x in range(assignment_count)]
        elif variant == "repeated_words":
            violations = [0 if x % 7 == 0 else accepted_code[(x*x + 3*x) % len(accepted_code)]
                          for x in range(assignment_count)]
        elif variant == "only_zero":
            violations = [0] * assignment_count
        elif variant == "no_zero":
            nonzero = accepted_code[1:]
            violations = [nonzero[x % len(nonzero)] for x in range(assignment_count)]
        else:
            raise AssertionError("unknown test variant")
        true_count = violations.count(0)
        candidates = parity_candidate_rows(length, samples)
        multiplicities = Counter(candidates)
        live = Counter(violations)
        false_sequence = [sum(count for word, count in live.items() if word)]
        chosen_rows = []
        for _ in range(3 * assignment_bits):
            old_false = false_sequence[-1]
            counts = {
                row: sum(count for word, count in live.items() if (row & word).bit_count() % 2 == 0)
                for row in multiplicities
            }
            average_false_numerator = sum(multiplicities[row] * (count - true_count)
                                          for row, count in counts.items())
            assert 4 * average_false_numerator <= 3 * len(candidates) * old_false
            # First list attaining the minimum, as in deterministic enumeration.
            best_row = min(candidates, key=lambda row: counts[row])
            live = Counter({word: count for word, count in live.items()
                            if (best_row & word).bit_count() % 2 == 0})
            new_false = sum(count for word, count in live.items() if word)
            assert 4 * new_false <= 3 * old_false
            assert live.get(0, 0) == true_count
            false_sequence.append(new_false)
            chosen_rows.append(best_row)
            rounds_checked += 1
        assert false_sequence[-1] == 0
        assert sum(live.values()) == true_count
        examples.append({
            "violation_vector_length": length, "row_list_length": samples,
            "assignment_bits": assignment_bits, "variant": variant,
            "candidate_lists_per_round": len(candidates),
            "distinct_candidate_rows": len(multiplicities),
            "true_count": true_count, "false_count_sequence": false_sequence,
            "chosen_rows_as_bitmasks": chosen_rows,
        })
    return {
        "status": "passed", "rounds_checked": rounds_checked,
        "claim_checked": "exact candidate-list average, deterministic three-quarter reduction, and final true count",
        "limitation": "synthetic violation multisets satisfying the required initial distance; these are not SAT instances",
        "examples": examples,
    }


def exact_parameters(density_bound: int) -> dict:
    """Return exact safe expander/code parameters without constructing them.

    Delta=1/(4096*B*ceil(log_2(2B))). The exponent t is the first
    integer satisfying (19/20)^t <= delta/2 and 16^t >= 64B.
    D is generally huge; return its bit length rather than all digits.
    """
    if density_bound < 1:
        raise ValueError("B must be positive")
    logarithm = ceil_log2_integer(2 * density_bound)
    delta_denominator = 4096 * density_bound * logarithm
    power = 0
    numerator = denominator = degree = 1
    while 2 * delta_denominator * numerator > denominator or degree < 64 * density_bound:
        numerator *= 19
        denominator *= 20
        degree *= 16
        power += 1
    assert 2 * delta_denominator * numerator <= denominator
    assert degree >= 64 * density_bound
    if power:
        assert (2 * delta_denominator * (numerator // 19) > denominator // 20
                or degree // 16 < 64 * density_bound)
    sampling_length = 2 * delta_denominator**2
    assert Fraction(1, sampling_length) == Fraction(1, 2 * delta_denominator**2)
    return {
        "B": density_bound, "ceil_log2_2B": logarithm,
        "delta_denominator": delta_denominator, "power_t": power,
        "degree_base": 16, "degree_bit_length": degree.bit_length(),
        "P": sampling_length,
    }


def check_exact_parameters() -> dict:
    records = [exact_parameters(bound) for bound in range(1, 1001)]
    padding_checks = 0
    # Padding and row-budget inequalities need no enormous graph. Check
    # them for several independently small regular degrees and densities.
    for bound in range(1, 9):
        for degree in (64 * bound, 64 * bound + 1, 128 * bound):
            local_rows = (degree + 64 * bound - 1) // (64 * bound)
            for clause_count in range(degree + 1, 4 * degree + 2):
                ratio_ceiling = (clause_count + degree - 1) // degree
                side_length = isqrt(ratio_ceiling)
                if side_length**2 < ratio_ceiling:
                    side_length += 1
                vertices_per_side = side_length**2
                edge_count = vertices_per_side * degree
                assert clause_count <= edge_count < 4 * clause_count
                row_count = 2 * vertices_per_side * local_rows
                assert 4 * bound * row_count < clause_count
                padding_checks += 1
    return {
        "status": "passed", "density_range": [1, 1000],
        "parameter_checks": len(records), "padding_row_budget_checks": padding_checks,
        "arithmetic": "integer powers and exact rational inequalities, no floating point",
        "limitation": "parameters are calculated, not instantiated as enormous graphs or local codes",
        "parameters": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification_results.json"))
    arguments = parser.parse_args()
    started = time.perf_counter()
    checks = {
        "graph_ports": check_graph_ports(),
        "finite_spectral_certificates": check_finite_spectral_certificates(),
        "codes_and_shortening": check_codes_and_shortening(),
        "subset_encoding": check_subset_encoding(),
        "greedy_parity": check_greedy_parity(),
        "exact_parameters": check_exact_parameters(),
    }
    result = {
        "status": "all_checks_passed",
        "purpose": "finite exact component verification for a density-sensitive reduction",
        "not_a_full_solver": True,
        "not_a_formal_proof": True,
        "external_theorems_not_verified_here": [
            "the source preprint's Boolean tensor-contraction theorem",
            "the Margulis--Gabber--Galil spectral bound for all graph sizes",
        ],
        "python_version": platform.python_version(),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "checks": checks,
    }
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "output": str(arguments.output.resolve()),
        "elapsed_seconds": result["elapsed_seconds"],
        "port_checks": checks["graph_ports"]["port_inversion_checks"],
        "exact_spectral_certificates": len(checks["finite_spectral_certificates"]["certificates"]),
        "rank_unrank_checks": checks["subset_encoding"]["rank_unrank_checks"],
        "wire_entropy_checks": checks["subset_encoding"]["wire_entropy_checks"],
        "greedy_rounds": checks["greedy_parity"]["rounds_checked"],
        "parameter_checks": checks["exact_parameters"]["parameter_checks"],
    }, indent=2))


if __name__ == "__main__":
    main()
