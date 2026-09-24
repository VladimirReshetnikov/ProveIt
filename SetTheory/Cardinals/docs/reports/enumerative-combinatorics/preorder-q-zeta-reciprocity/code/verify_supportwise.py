#!/usr/bin/env python3
"""Exact independent tests for the supportwise proof (Proof A, Engine 2).

Originally shipped as code/verify.py of preorder-q-zeta-supportwise;
renamed here so that the three verifiers of the merged package coexist.

Python 3.10+; standard library only. All mathematical checks use exact arithmetic.
Run from any directory:
    python code/verify_supportwise.py --output data/verification_supportwise.json
The tests are finite checks, not a replacement for the article's general proof.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import time
from typing import Iterable, Iterator, Sequence

Vector = tuple[int, ...]
Relation = tuple[int, ...]  # row i contains the j for which i <= j


def bits(mask: int) -> Iterator[int]:
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def weak_compositions(total: int, length: int) -> Iterator[Vector]:
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, length - 1):
            yield (first,) + rest


def closure(n: int, pairs: Iterable[tuple[int, int]]) -> Relation:
    rows = [1 << i for i in range(n)]
    for i, j in pairs:
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError("Relation index outside the ground set")
        rows[i] |= 1 << j
    for k in range(n):
        for i in range(n):
            if rows[i] >> k & 1:
                rows[i] |= rows[k]
    return tuple(rows)


def all_preorders(n: int) -> Iterator[Relation]:
    """Exhaust all reflexive relations and retain exactly the transitive ones."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    choices = []
    for i in range(n):
        other = [j for j in range(n) if j != i]
        choices.append(tuple((1 << i) | sum((1 << j) for k, j in enumerate(other)
                                           if mask >> k & 1)
                             for mask in range(1 << (n - 1))))
    for rows in product(*choices):
        if all(not (rows[j] & ~rows[i]) for i in range(n) for j in bits(rows[i])):
            yield rows


def ideal_bitset(rows: Relation) -> int:
    """Bit I is one precisely when the subset I is an order ideal."""
    n = len(rows)
    full = (1 << n) - 1
    return sum(1 << subset for subset in range(1 << n)
               if all(not (rows[i] & subset) for i in bits(full ^ subset)))


def support(vector: Vector) -> int:
    return sum(1 << i for i, value in enumerate(vector) if value)


class Prepared:
    """Precompute arithmetic independent of the preorder."""
    def __init__(self, n: int) -> None:
        self.n = n
        masks = range(1 << n)
        cache: dict[Vector, int] = {}

        def bad(vector: Vector) -> int:
            if vector not in cache:
                sums = [0] * (1 << n)
                result = 0
                for mask in range(1, 1 << n):
                    low = mask & -mask
                    sums[mask] = sums[mask ^ low] + vector[low.bit_length() - 1]
                    if sums[mask] > mask.bit_count():
                        result |= 1 << mask
                cache[vector] = result
            return cache[vector]

        self.pairs = [tuple((bad(tuple(((s >> i) & 1) + ((t >> i) & 1)
                                      for i in range(n))),
                            -1 if t.bit_count() % 2 else 1) for t in masks)
                      for s in masks]
        self.bases = tuple((vector, support(vector), bad(vector))
                           for vector in weak_compositions(n, n))
        self.points = tuple((vector, bad(vector)) for total in range(n + 1)
                            for vector in weak_compositions(total, n))

    def check(self, rows: Relation) -> list[int]:
        ideals = ideal_bitset(rows)
        counts = [0] * (1 << self.n)
        for _, s, bad in self.bases:
            if not (bad & ideals):
                counts[s] += 1
        for s, terms in enumerate(self.pairs):
            signed = sum(sign for bad, sign in terms if not (bad & ideals))
            predicted = ((-1) ** (self.n - s.bit_count())) * signed
            if predicted != counts[s]:
                raise AssertionError(("supportwise", rows, s, predicted, counts[s]))
            cofinal = all(rows[i] & s for i in range(self.n))
            if bool(counts[s]) != cofinal:
                raise AssertionError(("cofinality", rows, s, counts[s]))
        # Independent high-degree coefficient formulas.
        if self.n >= 1:
            top_minus_one = sum(counts[s] for s in range(1 << self.n)
                                if s.bit_count() == self.n - 1)
            if top_minus_one != sum(row.bit_count() - 1 for row in rows):
                raise AssertionError(("penultimate coefficient", rows))
        if self.n >= 2:
            formula = 0
            full = (1 << self.n) - 1
            for i in range(self.n):
                for j in range(i + 1, self.n):
                    s = full ^ (1 << i) ^ (1 << j)
                    a, b = (rows[i] & s).bit_count(), (rows[j] & s).bit_count()
                    c = (rows[i] & rows[j] & s).bit_count()
                    formula += a * b - c * (c - 1) // 2
            actual = sum(counts[s] for s in range(1 << self.n)
                         if s.bit_count() == self.n - 2)
            if actual != formula:
                raise AssertionError(("next coefficient", rows, actual, formula))
        return counts

    def lattice_points(self, rows: Relation) -> tuple[Vector, ...]:
        ideals = ideal_bitset(rows)
        return tuple(vector for vector, bad in self.points if not (bad & ideals))


def below(a: Vector, b: Vector) -> bool:
    return all(x <= y for x, y in zip(a, b))


def inverse_square(points: Sequence[Vector], diagonal: Sequence[Fraction]) -> Fraction:
    """Compute e_0^T (Z D)^(-2) 1 by two triangular solves, not by Mobius formulas."""
    n = len(points)
    successors = [tuple(j for j in range(i + 1, n) if below(points[i], points[j]))
                  for i in range(n)]

    def solve(rhs: Sequence[Fraction]) -> list[Fraction]:
        answer = [Fraction(0)] * n
        for i in range(n - 1, -1, -1):
            answer[i] = (rhs[i] - sum(diagonal[j] * answer[j] for j in successors[i])) / diagonal[i]
        return answer

    return solve(solve([Fraction(1)] * n))[0]


def check_matrices(prepared: Prepared, rows: Relation, counts: Sequence[int]) -> int:
    points = prepared.lattice_points(rows)
    n = prepared.n
    tests = 0
    for q in (Fraction(2), Fraction(3, 2)):
        actual = inverse_square(points, [q ** sum(x) for x in points])
        expected = ((-1) ** n) * sum(c * q ** (-s.bit_count()) for s, c in enumerate(counts))
        if actual != expected:
            raise AssertionError(("matrix", rows, q, actual, expected))
        tests += 1
    primes = (2, 3, 5, 7, 11, 13, 17, 19)
    diagonal = [Fraction(product_int(primes[i] ** x[i] for i in range(n))) for x in points]
    actual = inverse_square(points, diagonal)
    expected = ((-1) ** n) * sum(Fraction(c, product_int(primes[i] for i in bits(s)))
                               for s, c in enumerate(counts))
    if actual != expected:
        raise AssertionError(("multivariate matrix", rows, actual, expected))
    return tests + 1


def product_int(values: Iterable[int]) -> int:
    answer = 1
    for value in values:
        answer *= value
    return answer


def interpolate_value(nodes: Sequence[Fraction], values: Sequence[Fraction], at: Fraction) -> Fraction:
    total = Fraction(0)
    for i, value in enumerate(values):
        term = value
        for j, node in enumerate(nodes):
            if i != j:
                term *= (at - node) / (nodes[i] - node)
        total += term
    return total


def direct_interpolation(prepared: Prepared, rows: Relation, nonlinear: bool = False) -> dict:
    """Use only positive multichain values, then exact polynomial interpolation."""
    points = prepared.lattice_points(rows)
    q = Fraction(2)
    height = (lambda x: sum(x) ** 2) if nonlinear else sum
    degree = max(map(height, points))
    predecessors = [tuple(i for i, a in enumerate(points) if below(a, b)) for b in points]
    weights = [q ** height(x) for x in points]
    dp = weights[:]
    values = []
    for length in range(1, degree + 2):
        values.append(sum(dp))
        dp = [weights[j] * sum(dp[i] for i in predecessors[j]) for j in range(len(points))]
    nodes = [sum(q ** j for j in range(m)) for m in range(2, degree + 3)]
    actual = interpolate_value(nodes, values, -1 / q)
    counts = prepared.check(rows)
    expected = ((-1) ** prepared.n) * sum(c * q ** (-height(tuple((s >> i) & 1
                                                                        for i in range(prepared.n))))
                                        for s, c in enumerate(counts))
    if actual != expected:
        raise AssertionError(("positive interpolation", rows, actual, expected))
    return {"n": prepared.n, "relation_rows": list(rows), "height": "rank_squared" if nonlinear else "rank",
            "degree_bound": degree, "positive_samples": len(values), "q": "2", "answer": str(actual)}


def bipartite_check(neighbors: tuple[int, ...], s: int) -> None:
    """Three independent descriptions of the private-element Euler identity."""
    r = len(neighbors)
    independent = {0}
    for i, neighborhood in enumerate(neighbors):
        ground_neighbors = (1 << i) | (neighborhood << r)
        old = tuple(independent)
        for mask in old:
            for j in bits(ground_neighbors & ~mask):
                independent.add(mask | (1 << j))
    euler = ((-1) ** r) * sum((-1) ** mask.bit_count() for mask in independent)
    degrees = {(0,) * s}
    for neighborhood in neighbors:
        new = set()
        for vector in degrees:
            for j in bits(neighborhood):
                y = list(vector)
                y[j] += 1
                new.add(tuple(y))
        degrees = new
    if euler != len(degrees):
        raise AssertionError(("bipartite Euler", neighbors, s, euler, len(degrees)))
    # Interior points after subtracting the all-ones vector.
    if r == 0:
        return
    unions = [0] * (1 << r)
    for mask in range(1, 1 << r):
        low = mask & -mask
        unions[mask] = unions[mask ^ low] | neighbors[low.bit_length() - 1]
    interior = sum(1 for total in range(max(s, 0)) for y in weak_compositions(total, r)
                   if all(sum(y[i] for i in bits(mask)) < unions[mask].bit_count()
                          for mask in range(1, 1 << r)))
    if interior != euler:
        raise AssertionError(("interior", neighbors, s, interior, euler))


def run() -> dict:
    started = time.perf_counter()
    results: dict = {"arithmetic": "integers and fractions.Fraction; no floating point in tests",
                    "scope": "Finite checks only; general result depends on the written proof.",
                    "exhaustive_preorders": [], "sampled_preorders": [], "matrix_checks": 0}
    preparations = {}
    for n in range(6):
        prepared = preparations[n] = Prepared(n)
        count = support_checks = 0
        for rows in all_preorders(n):
            counts = prepared.check(rows)
            count += 1
            support_checks += 1 << n
            if n <= 4:
                results["matrix_checks"] += check_matrices(prepared, rows, counts)
        results["exhaustive_preorders"].append({"n": n, "preorders": count,
                                               "support_identities": support_checks})
        print(f"All labeled preorders n={n}: {count}; support identities {support_checks}", flush=True)
    rng = random.Random(26092049)
    results["random_seed"] = 26092049
    for n in (6, 7, 8):
        prepared = preparations[n] = Prepared(n)
        relations = set()
        while len(relations) < 64:
            # Arbitrary directed relations, or random block-preorders.
            if len(relations) % 2:
                labels = [rng.randrange(max(2, n - 1)) for _ in range(n)]
                probability = rng.choice((0.15, 0.35, 0.65))
                block_edges = {(a, b) for a in set(labels) for b in set(labels)
                               if a < b and rng.random() < probability}
                pairs = [(i, j) for i in range(n) for j in range(n)
                         if labels[i] == labels[j] or (labels[i], labels[j]) in block_edges]
            else:
                probability = rng.choice((0.03, 0.08, 0.15, 0.22))
                pairs = [(i, j) for i in range(n) for j in range(n)
                         if i != j and rng.random() < probability]
            rows = closure(n, pairs)
            relations.add(rows)
        for rows in sorted(relations):
            prepared.check(rows)
        results["sampled_preorders"].append({"n": n, "preorders": len(relations),
                                           "support_identities": len(relations) * (1 << n),
                                           "relation_rows": [list(rows) for rows in sorted(relations)]})
        print(f"Seeded sample n={n}: {len(relations)}", flush=True)
    graphs = 0
    for r in range(4):
        for s in range(5):
            for neighbors in product(range(1 << s), repeat=r):
                bipartite_check(neighbors, s)
                graphs += 1
    results["exhaustive_bipartite_graphs"] = {"r_range": [0, 3], "s_range": [0, 4], "graphs": graphs}
    for r, s in ((4, 4), (5, 4), (4, 5)):
        for _ in range(100):
            bipartite_check(tuple(rng.randrange(1 << s) for _ in range(r)), s)
    results["additional_bipartite_samples"] = 300
    examples = []
    for name, n, pairs in (
        ("antichain3", 3, []), ("chain3", 3, [(0, 1), (1, 2)]),
        ("V3", 3, [(0, 1), (0, 2)]), ("dual_V3", 3, [(0, 2), (1, 2)]),
        ("equivalence3", 3, [(0, 1), (1, 2), (2, 0)]),
        ("chain5", 5, [(i, i + 1) for i in range(4)]),
        ("equivalence5", 5, [(i, (i + 1) % 5) for i in range(5)]),
    ):
        rows = closure(n, pairs)
        p = preparations[n]
        counts = p.check(rows)
        poly = [sum(c for s, c in enumerate(counts) if s.bit_count() == k) for k in range(n + 1)]
        examples.append({"name": name, "n": n, "relation_rows": list(rows),
                         "points": len(p.lattice_points(rows)), "maxima": sum(counts),
                         "support_polynomial_coefficients": poly,
                         "support_counts": counts,
                         "positive_interpolation": direct_interpolation(p, rows)})
    results["examples"] = examples
    results["nonlinear_height_test"] = direct_interpolation(preparations[3], closure(3, [(0, 1), (1, 2)]), True)
    maxima = ((1, 1, 1), (3, 0, 0))
    points = tuple(sorted({x for b in maxima for x in product(*(range(v + 1) for v in b))},
                          key=lambda x: (sum(x), x)))
    actual = inverse_square(points, [Fraction(2) ** sum(x) for x in points])
    assert actual == Fraction(3, 8)
    results["pure_downset_counterexample"] = {"maxima": maxima, "q": 2,
                                              "actual": str(actual), "false_extension_rhs": "-5/8"}
    results["passed"] = True
    results["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data" / "verification_supportwise.json")
    args = parser.parse_args()
    results = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"PASS. Results written to {args.output}. Elapsed {results['elapsed_seconds']} seconds.")


if __name__ == "__main__":
    main()
