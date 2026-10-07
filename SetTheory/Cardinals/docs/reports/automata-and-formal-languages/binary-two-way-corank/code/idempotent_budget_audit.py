#!/usr/bin/env python3
"""Audit repetition-independent Brauer idempotent rank budgets.

The exact finite checks use literal graph multiplication from brauer_audit.py.
All pairs e,b of idempotents are exhausted through degree four, and every
distinct power of e*b*e is inspected until its first repetition. Reproducible
random cases extend through degree twelve, including families of several
idempotents, words with repetitions, and eventual power cycles. The graph
certificate is checked independently of the computed ranks of these words.

Run from any directory:
    python idempotent_budget_audit.py --output idempotent_budget_audit.json
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import random
from typing import Sequence

from brauer_audit import (
    cap_components,
    component_classification,
    matching_of_permutation,
    multiply,
    perfect_matchings,
    require,
    self_check_multiplication,
)

Diagram = tuple[int, ...]


def rank(a: Sequence[int]) -> int:
    n = len(a) // 2
    return sum(a[i] >= n for i in range(n))


def corank(a: Sequence[int]) -> int:
    return len(a) // 2 - rank(a)


def powers_until_periodic(a: Diagram) -> list[Diagram]:
    """All distinct positive powers, including every member of the final cycle."""
    result: list[Diagram] = []
    seen: set[Diagram] = set()
    power = a
    while power not in seen:
        seen.add(power)
        result.append(power)
        power = multiply(power, a)
    return result


def union_certificate(generators: Sequence[Diagram]) -> list[tuple[set[int], int]]:
    """Verify all hypotheses and componentwise edge budgets by exact graph work."""
    require(bool(generators), "Empty generator list")
    n = len(generators[0]) // 2
    adjacency: list[list[int]] = [[] for _ in range(n)]
    edges: list[tuple[int, int]] = []
    for a in generators:
        require(len(a) == 2 * n, "Mixed generator degrees")
        require(multiply(a, a) == a, "Non-idempotent generator")
        require(
            component_classification(a, cap_components(a)) is not None,
            "Idempotent classification failed in generator certificate",
        )
        for i in range(n):
            if i < a[i] < n:
                edges.append((i, a[i]))
                adjacency[i].append(a[i])
                adjacency[a[i]].append(i)
            if n + i < a[n + i]:
                j = a[n + i] - n
                edges.append((i, j))
                adjacency[i].append(j)
                adjacency[j].append(i)
    unseen = set(range(n))
    components: list[set[int]] = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        component, stack = {start}, [start]
        while stack:
            v = stack.pop()
            for u in adjacency[v]:
                if u in unseen:
                    unseen.remove(u)
                    component.add(u)
                    stack.append(u)
        components.append(component)
    result = []
    for component in components:
        edge_count = sum(i in component for i, _ in edges)
        require(edge_count % 2 == 0, "Union component has odd edge count")
        require(edge_count >= len(component) - 1, "Connectedness edge bound failed")
        require(
            edge_count >= 2 * (len(component) // 2),
            "Parity-rounded component budget failed",
        )
        for a in generators:
            require(
                all(a[i] % n in component for i in component),
                "Generator top edge leaves union component",
            )
            require(
                all(a[n + i] % n in component for i in component),
                "Generator bottom edge leaves union component",
            )
        result.append((component, edge_count))
    require(
        sum(count for _, count in result) == sum(corank(a) for a in generators),
        "Total generator edge budget failed",
    )
    return result


def check_word(
    word: Diagram,
    generators: Sequence[Diagram],
    certificate: Sequence[tuple[set[int], int]],
) -> None:
    n = len(word) // 2
    require(
        corank(word) <= sum(corank(a) for a in generators),
        f"Generator corank budget failed: generators={generators}; word={word}",
    )
    for component, edge_count in certificate:
        require(
            all(word[i] % n in component for i in component)
            and all(word[n + i] % n in component for i in component),
            "Computed word leaves invariant union component",
        )
        local_rank = sum(word[i] >= n for i in component)
        require(
            len(component) - local_rank <= edge_count,
            "Computed word violates componentwise edge budget",
        )


def exhaustive_order(n: int) -> dict[str, int]:
    diagrams = list(perfect_matchings(n))
    idempotents = [a for a in diagrams if multiply(a, a) == a]
    powers_checked = 0
    maximum_power_orbit = 0
    for e in idempotents:
        for b in idempotents:
            certificate = union_certificate((e, b))
            x = multiply(multiply(e, b), e)
            orbit = powers_until_periodic(x)
            maximum_power_orbit = max(maximum_power_orbit, len(orbit))
            for power in orbit:
                require(
                    rank(e) - rank(power) <= corank(b),
                    f"Corner-power bound failed at n={n}: e={e}, b={b}",
                )
                check_word(power, (e, b), certificate)
                powers_checked += 1

    # Exhaust all unordered distinct pairs of idempotent generators and every
    # element of their generated monoid. Direct products, never a predicted
    # component enumeration, determine this closure.
    generated_words_checked = 0
    two_generator_families = 0
    identity = matching_of_permutation(tuple(range(n)))
    for a, b in combinations(idempotents, 2):
        certificate = union_certificate((a, b))
        pending, seen = [identity], {identity}
        while pending:
            w = pending.pop()
            check_word(w, (a, b), certificate)
            generated_words_checked += 1
            for generator in (a, b):
                v = multiply(w, generator)
                if v not in seen:
                    seen.add(v)
                    pending.append(v)
        two_generator_families += 1
    return {
        "n": n,
        "diagrams": len(diagrams),
        "idempotents": len(idempotents),
        "ordered_corner_pairs": len(idempotents) ** 2,
        "corner_powers_checked": powers_checked,
        "maximum_corner_power_orbit": maximum_power_orbit,
        "two_generator_families": two_generator_families,
        "generated_words_checked": generated_words_checked,
    }


def diagram_on_blocks(n: int, blocks: Sequence[Sequence[int]]) -> Diagram:
    result = [-1] * (2 * n)

    def pair(x: int, y: int) -> None:
        require(result[x] == result[y] == -1, "Repeated port in block construction")
        result[x], result[y] = y, x

    for block in blocks:
        size = len(block)
        if size % 2:
            for j in range(0, size - 1, 2):
                pair(n + block[j], n + block[j + 1])
            for j in range(1, size - 1, 2):
                pair(block[j], block[j + 1])
            pair(block[0], n + block[-1])
        else:
            for j in range(0, size, 2):
                pair(block[j], block[j + 1])
            for j in range(1, size, 2):
                pair(n + block[j], n + block[(j + 1) % size])
    require(all(x >= 0 for x in result), "Block construction missed a port")
    diagram = tuple(result)
    require(multiply(diagram, diagram) == diagram, "Constructed diagram is not idempotent")
    return diagram


def random_idempotent(n: int, rng: random.Random, low_corank: bool) -> Diagram:
    labels = list(range(n))
    rng.shuffle(labels)
    blocks = []
    if low_corank and n >= 2:
        size = rng.choice([2] + ([3, 3, 3] if n >= 3 else []))
        blocks.append(labels[:size])
        blocks.extend([i] for i in labels[size:])
    else:
        while labels:
            options = [1, 1, 1, 1] + list(range(2, min(len(labels), 7) + 1))
            size = rng.choice(options)
            blocks.append(labels[:size])
            labels = labels[size:]
    return diagram_on_blocks(n, blocks)


def random_order(n: int, rng: random.Random, samples: int) -> dict[str, int]:
    corner_powers_checked = 0
    repeated_words_checked = 0
    repeated_word_powers_checked = 0
    nontrivial_budgets = 0
    maximum_power_orbit = 0
    generator_count_distribution: Counter[int] = Counter()
    identity = matching_of_permutation(tuple(range(n)))
    for sample in range(samples):
        e = identity if sample % 5 == 0 else random_idempotent(n, rng, sample % 3 == 0)
        b = random_idempotent(n, rng, sample % 4 != 0)
        certificate = union_certificate((e, b))
        orbit = powers_until_periodic(multiply(multiply(e, b), e))
        maximum_power_orbit = max(maximum_power_orbit, len(orbit))
        for power in orbit:
            require(rank(e) - rank(power) <= corank(b), "Random corner-power bound failed")
            check_word(power, (e, b), certificate)
            corner_powers_checked += 1

        count = rng.randrange(1, 4)
        generators = [e] + [random_idempotent(n, rng, True) for _ in range(count)]
        certificate = union_certificate(generators)
        generator_count_distribution[len(generators)] += 1
        if sum(corank(a) for a in generators) < n:
            nontrivial_budgets += 1
        word = identity
        for _ in range(60):
            word = multiply(word, rng.choice(generators))
            check_word(word, generators, certificate)
            require(
                rank(e) - rank(word) <= sum(corank(a) for a in generators[1:]),
                "Random relative rank budget failed",
            )
            repeated_words_checked += 1
        orbit = powers_until_periodic(word)
        maximum_power_orbit = max(maximum_power_orbit, len(orbit))
        for power in orbit:
            check_word(power, generators, certificate)
            repeated_word_powers_checked += 1
    return {
        "n": n,
        "random_corner_pairs": samples,
        "random_generator_families": samples,
        "corner_powers_checked": corner_powers_checked,
        "repeated_words_checked": repeated_words_checked,
        "repeated_word_powers_checked": repeated_word_powers_checked,
        "maximum_power_orbit": maximum_power_orbit,
        "families_with_budget_below_ambient_degree": nontrivial_budgets,
        "generator_count_distribution": dict(generator_count_distribution),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-max-n", type=int, default=4)
    parser.add_argument("--random-max-n", type=int, default=12)
    parser.add_argument("--samples-per-n", type=int, default=250)
    parser.add_argument("--seed", type=int, default=2026100707)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(0 <= args.exhaustive_max_n <= 5, "Exhaustive degree must lie in 0..5")
    require(args.random_max_n >= 0 and args.samples_per_n >= 1, "Invalid random range")
    self_check_multiplication()
    # A concrete non-idempotent counterexample checks the necessity of the
    # theorem's hypothesis: top cap 0--1, bottom cap 2'--3', through 2--0',3--1'.
    non_idempotent = (1, 0, 4, 5, 2, 3, 7, 6)
    require(corank(non_idempotent) == 2, "Counterexample initial corank incorrect")
    require(corank(multiply(non_idempotent, non_idempotent)) == 4,
            "Counterexample squared corank incorrect")
    exact = []
    for n in range(args.exhaustive_max_n + 1):
        row = exhaustive_order(n)
        exact.append(row)
        print(f"exhaustive n={n}: {row}", flush=True)
    rng = random.Random(args.seed)
    sampled = []
    for n in range(args.random_max_n + 1):
        row = random_order(n, rng, args.samples_per_n)
        sampled.append(row)
        print(f"sampled n={n}: {row}", flush=True)
    result = {
        "status": "pass",
        "seed": args.seed,
        "method": "literal graph multiplication; power orbits stopped at first repetition",
        "claims_checked": [
            "rank(e)-rank((e*b*e)^j) <= corank(b), all j, for all idempotent pairs through degree four",
            "corank(w) <= sum generator coranks for every word in every two-idempotent-generated monoid through degree four",
            "component invariance and even cap-edge budgets for all checked families",
            "relative corner and repeated-word rank budgets in reproducibly sampled families through degree twelve",
            "a concrete counterexample when the generator is not idempotent",
        ],
        "exhaustive": exact,
        "sampled": sampled,
        "totals": {
            "exhaustive_ordered_corner_pairs": sum(r["ordered_corner_pairs"] for r in exact),
            "exhaustive_corner_powers": sum(r["corner_powers_checked"] for r in exact),
            "exhaustive_two_generator_families": sum(r["two_generator_families"] for r in exact),
            "exhaustive_generated_words": sum(r["generated_words_checked"] for r in exact),
            "random_corner_pairs": sum(r["random_corner_pairs"] for r in sampled),
            "random_generator_families": sum(r["random_generator_families"] for r in sampled),
            "random_corner_powers": sum(r["corner_powers_checked"] for r in sampled),
            "random_repeated_words": sum(r["repeated_words_checked"] for r in sampled),
            "random_repeated_word_powers": sum(r["repeated_word_powers_checked"] for r in sampled),
        },
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(f"Certificate written to {args.output}", flush=True)


if __name__ == "__main__":
    main()
