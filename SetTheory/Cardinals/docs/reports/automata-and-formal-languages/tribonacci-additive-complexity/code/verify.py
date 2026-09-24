#!/usr/bin/env python3
"""Verify all finite certificates using exact standard-library arithmetic.

No numeric eigensolver, computer-algebra package, network access, or Walnut is
needed.  The article supplies the infinite-word and asymptotic arguments;
this program verifies their explicitly finite hypotheses.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import time

from tribonacci import (ROOT, LABELS, build_automaton, complexity, load_automaton,
                        morphism, prefix_counts, require, tribonacci_numbers)


def beta_times(vector: list[int]) -> list[int]:
    a, b, c = vector
    return [c, a + c, b + c]


def reachable(start: int, transitions: list[list[int]], allowed: set[int]) -> set[int]:
    seen = {start}
    queue = [start]
    for q in queue:
        for t in transitions[q]:
            if t in allowed and t not in seen:
                seen.add(t)
                queue.append(t)
    return seen


def polynomial_product(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def check_spectral(machine: dict) -> dict:
    transitions, outputs = machine["transitions"], machine["outputs"]
    size = len(transitions)
    component = {5, 9, 10, 11, *range(14, 76)}
    require(len(component) == 66, "Wrong recurrent component size")
    require(all(t < 0 or t in component for q in component for t in transitions[q]),
            "The recurrent component is not closed")
    reverse = [[] for _ in range(size)]
    for q, row in enumerate(transitions):
        for t in row:
            if t >= 0:
                reverse[t].append(q)
    require(reachable(5, transitions, component) == component,
            "Forward connectivity failed")
    require(reachable(5, reverse, component) == component,
            "Reverse connectivity failed")
    require(reachable(5, reverse, set(range(size))) == set(range(size)),
            "A live state cannot reach the recurrent component")
    require(transitions[62][0] == 62, "Expected a self-loop in the recurrent component")

    runs = []
    for row in transitions:
        if row[1] < 0:
            runs.append(2)
        elif transitions[row[1]][1] < 0:
            runs.append(1)
        else:
            runs.append(0)
    right = [[1, 0, 0], [-1, 1, 0], [-1, -1, 1]]
    for q, row in enumerate(transitions):
        require(runs[row[0]] == 0, "A zero must reset the trailing-one count")
        require((row[1] < 0) == (runs[q] == 2), "Illegal-word rule failed")
        if row[1] >= 0:
            require(runs[row[1]] == runs[q]+1, "Trailing-one transition failed")
        total = [sum(right[runs[t]][i] for t in row if t >= 0) for i in range(3)]
        require(total == beta_times(right[runs[q]]), "Right eigenvector failed")

    with (ROOT / "data" / "eigenvector.json").open(encoding="utf-8") as stream:
        data = json.load(stream)
    left, denominator = data["coefficients"], data["denominator"]
    require(len(left) == size and denominator == 44, "Left vector format failed")
    for q in range(size):
        total = [sum(left[t][i] for t in reverse[q]) for i in range(3)]
        require(total == beta_times(left[q]), f"Left eigenvector failed at {q}")
    require([sum(row[i] for row in left) for i in range(3)] == [44, 0, 0],
            "Left eigenvector is not normalized")
    aggregates = {label: [sum(left[q][i] for q in range(size) if outputs[q] == label)
                          for i in range(3)] for label in LABELS}
    require(aggregates == {1: [0, 0, 0], 3: [10, -76, 42],
                           4: [134, 144, -110], 5: [-100, -68, 68]},
            "Density aggregates failed")

    def reduced_product(a: list[int], b: list[int]) -> list[int]:
        product = polynomial_product(a, b)
        while len(product) > 3:
            coefficient = product.pop()
            for shift in (1, 2, 3):
                product[-shift] += coefficient
        return product + [0] * (3-len(product))

    scalar = [0, 0, 0]
    for q in range(size):
        product = reduced_product(left[q], right[runs[q]])
        scalar = [scalar[i] + product[i] for i in range(3)]
    require(scalar == [-220, -264, 220], "The left/right pairing failed")
    require(reduced_product([-5,-6,5], [2,7,3]) == [22,0,0],
            "The reciprocal pairing identity failed")
    require(all(any(left[q]) == (q in component) for q in range(size)),
            "The claimed support of the left eigenvector failed")

    factors = [[0]*45 + [1], [-1, 3, -3, 1], [1, 1, 1],
               [1, 0, 0, 0, -1, 0, 0, 0, 1], [-1, -1, -1, 1],
               [-1, 1, 1, 1], [1, -2, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 1]]
    polynomial = [1]
    for factor in factors:
        polynomial = polynomial_product(polynomial, factor)
    require(len(polynomial)-1 == 76, "Wrong annihilator degree")
    matrix = [[0]*size for _ in range(size)]
    # Horner evaluation, left-multiplying by the sparse matrix A at every step.
    for coefficient in reversed(polynomial):
        matrix = [[sum(matrix[t][j] for t in row if t >= 0) for j in range(size)]
                  for row in transitions]
        for q in range(size):
            matrix[q][q] += coefficient
    require(all(value == 0 for row in matrix for value in row),
            "The factored polynomial does not annihilate A")
    radius = Fraction(7, 5)
    separation = radius**12 - 2*radius**9 - 2*radius**5 - 2*radius - 1
    require(separation == Fraction(199057326, 244140625) and separation > 0,
            "The exact spectral-separation inequality failed")
    return {"live_states": size, "recurrent_component_size": len(component),
            "recurrent_output_counts": dict(Counter(outputs[q] for q in component)),
            "left_denominator": denominator, "aggregate_numerators": aggregates,
            "left_right_pairing": "5*beta^2-6*beta-5",
            "reciprocal_pairing": "(3*beta^2+7*beta+2)/22",
            "annihilator_degree": 76, "annihilator_matrix_is_zero": True,
            "spectral_radius_bound_other_than_beta": "7/5",
            "exact_separation_margin": str(separation)}


def check_all_factors(limit: int, machine: dict) -> dict:
    """Every n-factor is in an image of a legal adjacent pair, not a guessed prefix.

    All images have length >= limit.  Thus a factor crosses at most one image
    boundary.  The legal adjacent pairs are exactly 00,01,02,10,20.
    """
    images = {letter: letter for letter in "012"}
    depth = 0
    while min(map(len, images.values())) < limit:
        images = {letter: morphism(word) for letter, word in images.items()}
        depth += 1
    prefixes = []
    for pair in ("00", "01", "02", "10", "20"):
        word = images[pair[0]] + images[pair[1]]
        prefix = [0]
        for letter in word:
            prefix.append(prefix[-1] + int(letter))
        prefixes.append(prefix)
    checked_windows = 0
    for n in range(1, limit+1):
        values: set[int] = set()
        for prefix in prefixes:
            values.update(prefix[i+n] - prefix[i] for i in range(len(prefix)-n))
            checked_windows += len(prefix)-n
        require(len(values) == complexity(n, machine), f"All-factor mismatch at n={n}")
    return {"lengths_checked": limit, "substitution_depth": depth,
            "smallest_image_length": min(map(len, images.values())),
            "sliding_windows_examined": checked_windows,
            "coverage": "all factors, via five legal pair images"}


def check_counts(limit: int, machine: dict) -> dict:
    counts = {label: 0 for label in LABELS}
    probes = set(range(min(limit, 200)+1))
    probes.update(range(1000, limit+1, 1000))
    probes.add(limit)
    for n in range(limit+1):
        if n in probes:
            require(prefix_counts(n, machine) == counts, f"Digit-DP mismatch at N={n}")
        if n < limit:
            counts[complexity(n, machine)] += 1
    numbers = tribonacci_numbers(61)
    v = [0]*76
    v[0] = 1
    for k in range(61):
        expected = {label: sum(v[q] for q in range(76) if machine["outputs"][q] == label)
                    for label in LABELS}
        require(sum(v) == numbers[k], f"Tribonacci total mismatch at k={k}")
        require(prefix_counts(numbers[k], machine) == expected,
                f"Cutoff matrix mismatch at k={k}")
        following = [0]*76
        for q, row in enumerate(machine["transitions"]):
            for t in row:
                if t >= 0:
                    following[t] += v[q]
        v = following
    return {"individually_evaluated_n": limit, "prefix_count_probes": len(probes),
            "Tribonacci_cutoffs_checked": 61, "last_direct_counts": counts}


def check_generating_functions(machine: dict) -> dict:
    with (ROOT / "data" / "generating_functions.json").open(encoding="utf-8") as stream:
        functions = json.load(stream)
    degree = max(len(v["numerator"])-1 for v in functions.values())
    # A residual sequence also satisfies the verified degree-76 annihilator.
    # Checking 76 zero residuals after all numerator terms proves all later ones.
    through = degree + 76
    sequences = {label: [] for label in LABELS}
    vector = [0]*76
    vector[0] = 1
    for k in range(through+1):
        for label in LABELS:
            sequences[label].append(sum(vector[q] for q in range(76)
                                        if machine["outputs"][q] == label))
        following = [0]*76
        for q, row in enumerate(machine["transitions"]):
            for t in row:
                if t >= 0:
                    following[t] += vector[q]
        vector = following
    for label in LABELS:
        numerator = functions[str(label)]["numerator"]
        denominator = functions[str(label)]["denominator"]
        require(denominator[0] == 1, "Generating function is not normalized")
        for k in range(through+1):
            value = sum(d*sequences[label][k-i] for i,d in enumerate(denominator) if i <= k)
            target = numerator[k] if k < len(numerator) else 0
            require(value == target, f"Generating-function identity failed for {label}, k={k}")
    Q = [1,0,0,-2,0,0,0,-2,0,0,0,-2,1]
    common = polynomial_product(polynomial_product([1,-2,1], [1,-1,-1,-1]), Q)
    for label in (3,4,5):
        require(functions[str(label)]["denominator"] == common,
                "The claimed common generating-function denominator failed")
    divisor = [1,-1,-1,-1]
    ratio_denominator = polynomial_product(polynomial_product([1,-2,1],Q),[1,1,1])
    density_reversed = {3:[21,-38,5],4:[-55,72,67],5:[34,-34,-50]}
    for label in (3,4,5):
        left = [0,0]+[22*a for a in functions[str(label)]["numerator"]]
        right = polynomial_product(density_reversed[label],ratio_denominator)
        remainder = [0]*max(len(left),len(right))
        for i,a in enumerate(left): remainder[i] += a
        for i,a in enumerate(right): remainder[i] -= a
        while len(remainder) >= len(divisor):
            if remainder[-1]:
                multiple = -remainder[-1]
                shift = len(remainder)-len(divisor)
                for i,a in enumerate(divisor): remainder[i+shift] -= multiple*a
            remainder.pop()
        require(all(a == 0 for a in remainder), "Independent residue-density check failed")
    return {"coefficient_identities_checked_through_k":through,
            "successive_zero_residuals_after_numerators":76,
            "common_denominator_degree":17,
            "density_residue_identities": "all three exact polynomial remainders are zero"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factor-limit", type=int, default=2048)
    parser.add_argument("--count-limit", type=int, default=100000)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "data" / "verification_results.json")
    args = parser.parse_args()
    start = time.perf_counter()
    try:
        require(args.factor_limit >= 1 and args.count_limit >= 1, "Limits must be positive")
        stored = load_automaton()
        rebuilt, certificate = build_automaton()
        for field in ("initial", "transitions", "outputs"):
            require(rebuilt[field] == stored[field], f"Reconstruction differs in {field}")
        require(len(certificate["pairs"]) == 56 and len(certificate["sets"]) == 277,
                "Unexpected co-decomposition closure size")
        require(len(certificate["product_states"]) == 296,
                "Unexpected valid-product closure size")
        with (ROOT / "data" / "co_decomposition.json").open(encoding="utf-8") as stream:
            require(json.load(stream) == certificate, "Stored co-decomposition certificate differs")
        with (ROOT / "data" / "selection.json").open(encoding="utf-8") as stream:
            selection = json.load(stream)
        require(hashlib.sha256("\n".join(selection["ordered_areas"]).encode()).hexdigest()
                == selection["list_sha256"], "Random-area list digest mismatch")
        require(selection["ordered_areas"][selection["zero_based_index"]]
                == selection["area"] == "Combinatorics on words", "Area record mismatch")
        report = {"status": "PASS", "python_version": platform.python_version(),
                  "co_decomposition_pairs": 56, "co_decomposition_sets": 277,
                  "valid_product_states": 296,
                  "spectral_certificates": check_spectral(stored),
                  "all_factor_crosscheck": check_all_factors(args.factor_limit, stored),
                  "counting_crosscheck": check_counts(args.count_limit, stored),
                  "generating_function_crosscheck": check_generating_functions(stored),
                  "random_selection_record_consistent": True,
                  "elapsed_seconds": round(time.perf_counter()-start, 3),
                  "scope": "Exact finite certificates; not a proof-assistant formalization"}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print(json.dumps(report, indent=2))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"VERIFICATION FAILED: {error}\n")


if __name__ == "__main__":
    main()
