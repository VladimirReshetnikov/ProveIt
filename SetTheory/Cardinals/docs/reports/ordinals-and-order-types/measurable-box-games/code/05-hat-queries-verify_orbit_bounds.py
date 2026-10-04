#!/usr/bin/env python3
"""Finite certificates for the hat-score orbit bounds, using only Python stdlib.

Run:
    python3 verify_orbit_bounds.py

The script exhausts every deterministic strategy profile in which each player
uses zero or one other hat, for n = 1, ..., 5.  It then constructs the binary
labels used in the sparse-support proof and verifies their character sums and
the actual score orbit averages on representative nonlinear games.  These are
finite verification certificates; the dimension-independent theorem is proved
in the accompanying article.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from time import perf_counter


class VerificationError(RuntimeError):
    """A finite verification certificate failed a required check."""


def require(condition: bool, message: str) -> None:
    """Check a certificate condition, including when Python runs with -O."""
    if not condition:
        raise VerificationError(message)


def configurations(n: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.product((-1, 1), repeat=n))


def fraction_record(numerator: int, denominator: int) -> dict[str, object]:
    value = Fraction(numerator, denominator)
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "exact": str(value),
    }


def one_query_exhaustion(n: int) -> dict[str, object]:
    hats = configurations(n)
    descriptions: list[list[dict[str, object]]] = []
    vectors: list[list[tuple[int, ...]]] = []
    for i in range(n):
        own_descriptions: list[dict[str, object]] = []
        own_vectors: list[tuple[int, ...]] = []
        for sign in (1, -1):
            own_descriptions.append({"kind": "constant", "sign": sign})
            own_vectors.append(tuple(sign * x[i] for x in hats))
        for j in range(n):
            if j == i:
                continue
            for sign in (1, -1):
                own_descriptions.append(
                    {"kind": "signed_other_hat", "observed_player": j + 1,
                     "sign": sign}
                )
                own_vectors.append(tuple(sign * x[i] * x[j] for x in hats))
        require(len(own_vectors) == 2 * n,
                f"n={n}, player={i + 1}: expected exactly {2 * n} legal rules")
        descriptions.append(own_descriptions)
        vectors.append(own_vectors)

    histogram: Counter[int] = Counter()
    best_bad = len(hats) + 1
    witness: tuple[int, ...] | None = None
    profile_count = 0
    for profile in itertools.product(range(2 * n), repeat=n):
        score_vectors = tuple(vectors[i][choice] for i, choice in enumerate(profile))
        bad_count = sum(total <= 0 for total in map(sum, zip(*score_vectors)))
        histogram[bad_count] += 1
        profile_count += 1
        if bad_count < best_bad:
            best_bad = bad_count
            witness = profile

    expected_profiles = (2 * n) ** n
    require(profile_count == expected_profiles,
            f"n={n}: enumerated {profile_count} profiles, expected {expected_profiles}")
    require(sum(histogram.values()) == expected_profiles,
            f"n={n}: the profile histogram does not cover every strategy profile")
    require(4 * best_bad >= len(hats),
            f"n={n}: exhaustive minimum violates the one-query bound 1/4")
    require(witness is not None,
            f"n={n}: no strategy attaining the enumerated minimum was recorded")
    witness_description = [
        {"player": i + 1, **descriptions[i][choice]}
        for i, choice in enumerate(witness)
    ]
    return {
        "n": n,
        "rules_per_player": 2 * n,
        "strategy_profiles": profile_count,
        "hat_assignments_per_profile": len(hats),
        "profile_assignment_pairs": profile_count * len(hats),
        "minimum_nonpositive_probability": fraction_record(best_bad, len(hats)),
        "attaining_profiles": histogram[best_bad],
        "witness": witness_description,
        "nonpositive_count_histogram": {
            str(k): histogram[k] for k in sorted(histogram)
        },
    }


@dataclass(frozen=True)
class Rule:
    owner: int
    visible: tuple[int, ...]
    truth_table: tuple[int, ...]
    description: str

    def predict(self, x: tuple[int, ...]) -> int:
        index = 0
        for j in self.visible:
            index = 2 * index + (x[j] == 1)
        return self.truth_table[index]

    def score_support(self) -> dict[frozenset[int], Fraction]:
        """Compute the Walsh expansion by its exact finite inner products."""
        m = len(self.visible)
        local_hats = configurations(m)
        support: dict[frozenset[int], Fraction] = {}
        for mask in range(1 << m):
            numerator = 0
            for y, prediction in zip(local_hats, self.truth_table):
                character = 1
                for j in range(m):
                    if mask & (1 << j):
                        character *= y[j]
                numerator += prediction * character
            if numerator:
                edge = frozenset(
                    [self.owner] + [self.visible[j] for j in range(m)
                                    if mask & (1 << j)]
                )
                support[edge] = Fraction(numerator, 1 << m)
        return support


def nand_game(n: int, visibility: int) -> tuple[Rule, ...]:
    return tuple(
        Rule(
            owner=i,
            visible=tuple((i + j) % n for j in range(1, visibility + 1)),
            truth_table=tuple(-1 if all(value == 1 for value in y) else 1
                              for y in configurations(visibility)),
            description="Predict -1 exactly when all visible hats are +1.",
        )
        for i in range(n)
    )


def adaptive_depth_two_game(n: int) -> tuple[Rule, ...]:
    return tuple(
        Rule(
            owner=i,
            visible=tuple((i + j) % n for j in (1, 2, 3)),
            truth_table=tuple(y[1] if y[0] == 1 else y[2]
                              for y in configurations(3)),
            description=("Query the first listed hat. If it is +1, query and "
                         "copy the second; otherwise query and copy the third."),
        )
        for i in range(n)
    )


def xor_labels(n: int, edges: set[frozenset[int]], bound: int) -> dict[str, object]:
    """Implement the hereditary-degree peeling proof over a binary vector space."""
    rank = bound.bit_length()  # 2**rank is the first power of two greater than B.
    group_size = 1 << rank
    remaining = set(range(n))
    peeling: list[tuple[int, int]] = []
    while remaining:
        current_edges = [edge for edge in edges if edge <= remaining]
        degrees = {v: sum(v in edge for edge in current_edges) for v in remaining}
        vertex = min(remaining, key=lambda v: (degrees[v], v))
        require(degrees[vertex] <= bound,
                f"Peeling vertex {vertex + 1}: degree {degrees[vertex]} exceeds {bound}")
        peeling.append((vertex, degrees[vertex]))
        remaining.remove(vertex)

    labels: dict[int, int] = {}
    for vertex, _degree in reversed(peeling):
        forbidden: set[int] = set()
        for edge in edges:
            if vertex not in edge or not (edge - {vertex}) <= labels.keys():
                continue
            value = 0
            for other in edge - {vertex}:
                value ^= labels[other]
            forbidden.add(value)
        require(len(forbidden) <= bound < group_size,
                f"Labeling vertex {vertex + 1}: {len(forbidden)} forbidden labels, "
                f"bound={bound}, group_size={group_size}")
        labels[vertex] = next(value for value in range(group_size)
                              if value not in forbidden)

    support_xors: list[dict[str, object]] = []
    for edge in sorted(edges, key=lambda e: (len(e), tuple(sorted(e)))):
        value = 0
        for vertex in edge:
            value ^= labels[vertex]
        require(value != 0,
                f"Support {sorted(edge)} has zero XOR under the constructed labels")
        support_xors.append({"players": [i + 1 for i in sorted(edge)], "xor": value})

    maximum_density = Fraction(0)
    for mask in range(1, 1 << n):
        subset = {j for j in range(n) if mask & (1 << j)}
        mass = sum(len(edge) for edge in edges if edge <= subset)
        require(mass <= bound * len(subset),
                f"Vertex subset {sorted(subset)}: support mass {mass} exceeds "
                f"the bound {bound * len(subset)}")
        maximum_density = max(maximum_density, Fraction(mass, len(subset)))

    return {
        "dimension": rank,
        "group_size": group_size,
        "labels_in_player_order": [labels[i] for i in range(n)],
        "peeling_order": [v + 1 for v, _degree in peeling],
        "peeling_degrees": [degree for _v, degree in peeling],
        "all_nonempty_vertex_subsets_checked": (1 << n) - 1,
        "maximum_induced_support_density": str(maximum_density),
        "support_xors": support_xors,
    }


def verify_representative(name: str, rules: tuple[Rule, ...], bound: int,
                          model: dict[str, object]) -> dict[str, object]:
    n = len(rules)
    supports = [rule.score_support() for rule in rules]
    owned_masses = [sum(map(len, support)) for support in supports]
    require(max(owned_masses) <= bound,
            f"{name}: owned support masses {owned_masses} exceed the bound {bound}")
    edges = set().union(*supports)
    certificate = xor_labels(n, edges, bound)
    labels = certificate["labels_in_player_order"]
    group_size = certificate["group_size"]
    require(isinstance(labels, list) and isinstance(group_size, int),
            f"{name}: malformed label certificate or group size")

    score_histogram: Counter[int] = Counter()
    orbit_sums_checked = 0
    character_sums_checked = 0
    for edge in edges:
        total = 0
        for a in range(group_size):
            sign = 1
            for j in edge:
                if (a & labels[j]).bit_count() % 2:
                    sign = -sign
            total += sign
        require(total == 0,
                f"{name}: support {sorted(edge)} has character sum {total}, not zero")
        character_sums_checked += 1

    for x in configurations(n):
        score = sum(x[rule.owner] * rule.predict(x) for rule in rules)
        score_histogram[score] += 1
        fourier_score = sum(
            coefficient * product(x[j] for j in edge)
            for support in supports for edge, coefficient in support.items()
        )
        require(fourier_score == score,
                f"{name}, hats={x}: Walsh reconstruction {fourier_score} "
                f"differs from the direct score {score}")
        orbit_sum = 0
        has_nonpositive = False
        has_nonnegative = False
        for a in range(group_size):
            transformed = tuple(
                -x[j] if (a & labels[j]).bit_count() % 2 else x[j]
                for j in range(n)
            )
            value = sum(transformed[rule.owner] * rule.predict(transformed)
                        for rule in rules)
            orbit_sum += value
            has_nonpositive |= value <= 0
            has_nonnegative |= value >= 0
        require(orbit_sum == 0,
                f"{name}, hats={x}: actual score orbit sum is {orbit_sum}, not zero")
        require(has_nonpositive and has_nonnegative,
                f"{name}, hats={x}: the orbit lacks a nonpositive or nonnegative score")
        orbit_sums_checked += 1

    nonpositive = sum(count for value, count in score_histogram.items() if value <= 0)
    require(group_size * nonpositive >= (1 << n),
            f"{name}: observed nonpositive probability violates 1/{group_size}")
    return {
        "name": name,
        "players": n,
        "model": model,
        "owned_support_masses": owned_masses,
        "theorem_mass_bound": bound,
        "distinct_score_supports": len(edges),
        "rules": [{"player": r.owner + 1,
                   "visible_players": [j + 1 for j in r.visible],
                   "description": r.description,
                   "truth_table_in_lexicographic_sign_order": list(r.truth_table)}
                  for r in rules],
        "label_certificate": certificate,
        "character_sums_checked": character_sums_checked,
        "configuration_orbit_sums_checked": orbit_sums_checked,
        "configuration_group_pairs_checked": orbit_sums_checked * group_size,
        "score_histogram": {str(value): score_histogram[value]
                            for value in sorted(score_histogram)},
        "nonpositive_probability": fraction_record(nonpositive, 1 << n),
        "certified_lower_bound": fraction_record(1, group_size),
    }


def product(values) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("orbit_verification.json"))
    args = parser.parse_args()
    started = perf_counter()
    exhaustive = [one_query_exhaustion(n) for n in range(1, 6)]
    representatives = [
        verify_representative("nonadaptive_d2_cyclic_nand", nand_game(5, 2), 8,
                              {"kind": "fixed_visibility", "visibility": 2}),
        verify_representative("nonadaptive_d3_cyclic_nand", nand_game(7, 3), 20,
                              {"kind": "fixed_visibility", "visibility": 3}),
        verify_representative("adaptive_depth2_multiplexer",
                              adaptive_depth_two_game(5), 10,
                              {"kind": "adaptive_decision_tree", "depth": 2,
                               "potentially_queried_hats_per_player": 3}),
    ]
    result = {
        "status": "all_assertions_passed",
        "python_dependencies": "standard library only",
        "score_convention": "F = sum_i X_i f_i; D = F/2",
        "exhaustive_one_query_games": exhaustive,
        "total_strategy_profiles": sum(r["strategy_profiles"] for r in exhaustive),
        "total_profile_assignment_pairs": sum(r["profile_assignment_pairs"]
                                               for r in exhaustive),
        "sparse_support_representatives": representatives,
        "elapsed_seconds": round(perf_counter() - started, 6),
        "scope": ("Finite certificates only. The universal bounds, infinite-game "
                  "conclusions, and expected-query threshold require the proofs "
                  "in the article."),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "output": str(args.output.resolve()),
        "strategy_profiles": result["total_strategy_profiles"],
        "profile_assignment_pairs": result["total_profile_assignment_pairs"],
        "minimum_nonpositive_probabilities": {
            str(r["n"]): r["minimum_nonpositive_probability"]["exact"]
            for r in exhaustive
        },
        "representative_games": len(representatives),
        "elapsed_seconds": result["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
