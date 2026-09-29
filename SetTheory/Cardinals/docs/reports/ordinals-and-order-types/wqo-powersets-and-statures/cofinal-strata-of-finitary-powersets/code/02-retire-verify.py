#!/usr/bin/env python3
"""Deterministic finite checks for the retirement-path implementation.

No finite test here proves a transfinite theorem or establishes novelty.
The article supplies the mathematical upper and lower bounds separately.
"""
from __future__ import annotations

from collections import Counter
from itertools import product, combinations
import json
from pathlib import Path
import platform
import time

from retirement import (Ordinal, Poset, ZERO, ONE, bits, certificate, expand_limit_fibres,
                        height, maximum_weight, natural_sum, ordinal_sum, path_cost)

COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str) -> None:
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(f"failed {category} check #{COUNTS[category]}")


def natural_posets(n: int):
    """Each transitively closed relation compatible with 0<...<n-1 once."""
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        rows = [1 << i for i in range(n)]
        edges = []
        for k, (i, j) in enumerate(pairs):
            if mask >> k & 1:
                rows[i] |= 1 << j
                edges.append((i, j))
        if all(not (rows[i] >> j & 1) or rows[j] & ~rows[i] == 0
               for i in range(n) for j in range(i + 1, n)):
            yield Poset(n, edges)


def word_oracle(exponents):
    """Independent ordinary-sum evaluator on monomial words (stack erasure)."""
    word = []
    for exponent in exponents:
        while word and word[-1] < exponent:
            word.pop()
        word.append(exponent)
    terms = []
    for exponent in word:
        if terms and terms[-1][0] == exponent:
            terms[-1] = (exponent, terms[-1][1] + 1)
        else:
            terms.append((exponent, 1))
    return Ordinal(tuple(terms))


def oracle_cost(path, exponents):
    groups = [a & ~b for a, b in zip(path, path[1:])] + [path[-1]]
    return word_oracle([max(exponents[q] for q in bits(group)) for group in groups])


def weighted_case(p, exponents, all_chains=None):
    actual, path = height(p, exponents)
    covered, cover_path = height(p, exponents, cover_only=True)
    check(actual == covered, "full_DP_equals_cover_DP")
    check(actual == path_cost(path, exponents) == oracle_cost(path, exponents),
          "path_cost_certificate")
    check(covered == oracle_cost(cover_path, exponents), "cover_path_certificate")
    check(all(b in p.covers[a] for a, b in zip(cover_path, cover_path[1:])),
          "certificate_is_saturated")
    check(cover_path[-1] == next(a for a in p.frontiers if not p.successors[a]),
          "certificate_ends_at_top")
    lower = max(Ordinal.mono(e) for e in exponents)
    upper = natural_sum(Ordinal.mono(e) for e in exponents)
    check(lower <= actual <= upper, "universal_bounds")
    check(sum(c for _, c in actual.terms) <= p.n, "coefficient_budget")
    check(actual.terms[0][0] == max(exponents), "leading_exponent")
    if all_chains is not None:
        brute = max(oracle_cost(chain, exponents) for chain in all_chains)
        check(actual == brute, "DP_equals_independent_all_chain_oracle")
    labels = {e: 2 * e + 1 for e in set(exponents)}
    renamed, _ = height(p, [labels[e] for e in exponents])
    check(renamed == actual.relabel(labels), "exponent_order_invariance")


def profiles(p):
    for a in p.antichains:
        support = tuple(bits(a))
        for values in product(range(3), repeat=len(support)):
            yield a, dict(zip(support, values))


def profile_le(p, x, y):
    a, xv = x
    b, yv = y
    return p.hoare(a, b) and all(xv[q] <= yv[q] for q in bits(a & b))


def normalize(p, profile):
    a, values = profile
    c = p.complete(a)
    return c, {q: values[q] + 1 if q in values else 0 for q in bits(c)}


def test_profiles(p):
    values = list(profiles(p))
    normalized = [normalize(p, x) for x in values]
    for i, x in enumerate(values):
        for j, y in enumerate(values):
            if i != j and profile_le(p, x, y):
                check(normalized[i] != normalized[j]
                      and profile_le(p, normalized[i], normalized[j]),
                      "strict_profile_normalization")


def test_structure(p, all_chains):
    complete = {a: p.complete(a) for a in p.antichains}
    for a in p.antichains:
        check(complete[a] in p.frontiers and (complete[a] & a) == a,
              "maximal_completion")
        for b in p.antichains:
            if p.hoare(a, b):
                check(p.hoare(complete[a], complete[b]), "completion_monotonicity")
                check((a & ~b) & complete[b] == 0, "strict_retirement_property")
    for path in all_chains:
        union = 0
        seen = 0
        groups = [a & ~b for a, b in zip(path, path[1:])] + [path[-1]]
        for a in path:
            union |= a
        for group in groups:
            check(bool(group) and not group & seen, "disjoint_nonempty_retirement_groups")
            seen |= group
        check(seen == union, "retirement_partition")
    longest = {}
    for a in reversed(p.topological):
        longest[a] = 1 + max([longest[b] for b in p.successors[a]], default=0)
    uniform, _ = height(p, [1] * p.n)
    check(uniform == Ordinal.mono(1, max(longest.values())), "uniform_recovery")


def product_limit_oracle(fibres):
    """Independent standard height formula for a product of limit ordinals."""
    prefixes = []
    tails = []
    for fibre in fibres:
        *initial, (e, c) = fibre.terms
        if c > 1:
            initial.append((e, c - 1))
        prefixes.append(Ordinal(tuple(initial)))
        tails.append(Ordinal.mono(e))
    return natural_sum(prefixes) + max(tails)


def test_limits():
    choices = [Ordinal(((1, 1),)), Ordinal(((1, 2),)), Ordinal(((2, 1),)),
               Ordinal(((2, 1), (1, 1))), Ordinal(((2, 2),)),
               Ordinal(((3, 1), (1, 2)))]
    for n in range(1, 4):
        for fibres in product(choices, repeat=n):
            chain = Poset(n, [(i, i + 1) for i in range(n - 1)])
            expanded, exponents, _ = expand_limit_fibres(chain, fibres)
            result, _ = height(expanded, exponents)
            check(result == ordinal_sum(fibres), "limit_fibre_chain_expansion")
            anti = Poset(n, [])
            expanded, exponents, _ = expand_limit_fibres(anti, fibres)
            result, _ = height(expanded, exponents)
            check(result == product_limit_oracle(fibres), "limit_fibre_product_oracle")


def test_retirement_prefix_maps():
    # One coordinate per group is sufficient to test stage bookkeeping; additionally
    # use two coordinates per group to test natural-sum residual interactions.
    cases = [(1, 2, 1), (2, 1, 2), (3, 1, 2), (1, 3, 2, 3), (2, 2, 1)]
    for group_exponents in cases:
        for multiplicity in (1, 2):
            groups = [list(range(i * multiplicity, (i + 1) * multiplicity))
                      for i in range(len(group_exponents))]
            exponents = [e for e in group_exponents for _ in range(multiplicity)]
            maximum = max(group_exponents)
            last = max(i for i, e in enumerate(group_exponents) if e == maximum)
            k = group_exponents.count(maximum)
            upper = Ordinal.mono(maximum, k)
            states = []
            # Sparse deterministic values keep the test small and include infinite
            # ordinals at every possible smaller leading exponent.
            for stage in range(last + 1):
                active = [q for group in groups[stage:] for q in group]
                samples = [[ZERO, ONE, Ordinal.mono(e - 1)] if e > 1 else [ZERO, ONE]
                           for e in (exponents[q] for q in active)]
                for sample in product(*samples):
                    vector = [Ordinal.mono(exponents[q]) if q < stage * multiplicity else ZERO
                              for q in range(len(exponents))]
                    for q, value in zip(active, sample):
                        vector[q] = value
                    c = sum(group_exponents[i] == maximum for i in range(stage))
                    residual_terms = [vector[q] for q in active]
                    residual_terms.extend(Ordinal.mono(exponents[q])
                                          for i in range(stage) if group_exponents[i] < maximum
                                          for q in groups[i])
                    mapped = (Ordinal.mono(maximum, c) if c else ZERO) + natural_sum(residual_terms)
                    check(mapped < upper, "prefix_rank_range")
                    states.append((stage, tuple(vector), mapped))
            # Full pairs could be large: compare each state with a fixed deterministic
            # sample of target states, plus every same-stage immediate coordinate rise.
            stride = max(1, len(states) // 100)
            for a in states:
                for b in states[::stride]:
                    if a[1] != b[1] and all(x <= y for x, y in zip(a[1], b[1])):
                        check(a[2] < b[2], "prefix_rank_strictness")


def main():
    started = time.monotonic()
    for length in range(7):
        for word in product(range(4), repeat=length):
            check(ordinal_sum(Ordinal.mono(e) for e in word) == word_oracle(word),
                  "ordinal_addition_word_oracle")
    for x, y in [(Ordinal(((2, 1), (1, 2))), Ordinal(((2, 2),)))]:
        check(x < y, "CNF_lexicographic_comparison")
    check(height(Poset(0, []), [])[0] == ONE, "empty_skeleton")
    census = {}
    weighted = 0
    for n in range(1, 7):
        count = 0
        for p in natural_posets(n):
            count += 1
            all_chains = p.chains()
            test_structure(p, all_chains)
            if n <= 4:
                test_profiles(p)
            assignments = product(range(1, 4), repeat=n) if n <= 5 else (
                (1,) * n, (2,) * n, (3,) * n, tuple(range(1, n + 1)),
                tuple(range(n, 0, -1)), tuple(1 + (i % 2) for i in range(n)),
                tuple(1 + ((i + 1) % 2) for i in range(n)), (3, 1, 2, 3, 2, 1))
            for exponents in assignments:
                weighted_case(p, exponents, all_chains if n <= 5 else None)
                weighted += 1
        census[n] = count
        print(f"n={n}: {count} naturally labelled posets", flush=True)
    check(list(census.values()) == [1, 2, 7, 40, 357, 4824], "poset_census")
    test_limits()
    test_retirement_prefix_maps()
    examples = {
        "persistent_large_coordinate": {"n": 3, "edges": [[1, 2]], "exponents": [2, 1, 1]},
        "retiring_large_coordinates": {"n": 3, "edges": [[1, 2]], "exponents": [1, 2, 2]},
        "uniform_N": {"n": 4, "edges": [[0, 2], [1, 2], [1, 3]], "exponents": [1, 1, 1, 1]},
        "mixed_N": {"n": 4, "edges": [[0, 2], [1, 2], [1, 3]], "exponents": [2, 1, 1, 2]},
        "branching_frontiers": {"n": 4, "edges": [[0, 2], [1, 3]], "exponents": [2, 1, 1, 1]},
    }
    expected = {"persistent_large_coordinate": Ordinal(((2, 1),)),
                "retiring_large_coordinates": Ordinal(((2, 2),)),
                "uniform_N": Ordinal(((1, 3),)), "mixed_N": Ordinal(((2, 2),)),
                "branching_frontiers": Ordinal(((2, 1), (1, 2)))}
    data = Path(__file__).resolve().parent.parent / "data"
    for name, spec in examples.items():
        p = Poset(spec["n"], spec["edges"])
        value, _ = height(p, spec["exponents"])
        check(value == expected[name], "displayed_examples")
        (data / f"{name}.json").write_text(json.dumps(spec, indent=2) + "\n")
        (data / f"{name}_certificate.json").write_text(
            json.dumps(certificate(p, spec["exponents"]), indent=2) + "\n")
    limit_example = {"n": 2, "edges": [], "fibres_cnf": [[[2, 1], [1, 1]], [[3, 1], [2, 1]]]}
    (data / "limit_fibres.json").write_text(json.dumps(limit_example, indent=2) + "\n")
    result = {
        "status": "passed", "python": platform.python_version(),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "naturally_labelled_posets_by_size": census,
        "nonempty_posets": sum(census.values()), "weighted_cases": weighted,
        "assertions_by_category": dict(sorted(COUNTS.items())),
        "total_assertions": sum(COUNTS.values()),
        "limitations": "Finite combinatorial and implementation checks only; not a formal proof, "
                       "not a computation of infinite descending-tree ranks, and not a novelty certificate."
    }
    (data / "verification_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
