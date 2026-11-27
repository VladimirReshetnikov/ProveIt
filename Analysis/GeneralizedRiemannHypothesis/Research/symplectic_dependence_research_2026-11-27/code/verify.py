#!/usr/bin/env python3
"""Independent exact verification of symplectic cycle and cactus laws.

The observed laws below are obtained by enumerating every assignment of
actual nonzero vectors to vertices. No trace formula or proposed probability
law is used to generate the observed counts. All comparisons use Fraction.
GF(4) is GF(2)[z]/(z^2+z+1), with polynomial coefficients encoded in bits.

Usage: python3 verify.py [--output PATH]
Python standard library only.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path
import platform
import time


class Field:
    def __init__(self, q: int):
        if q not in (2, 3, 4, 5, 7):
            raise ValueError("Supported q: 2, 3, 4, 5, 7")
        self.q = q
        self.p = 2 if q == 4 else q
        self.add_table = [[(a ^ b) if q == 4 else (a + b) % q
                           for b in range(q)] for a in range(q)]
        self.mul_table = [[self._mul(a, b) for b in range(q)] for a in range(q)]
        self.neg_table = [a if q == 4 else (-a) % q for a in range(q)]

    def _mul(self, a: int, b: int) -> int:
        if self.q != 4:
            return a * b % self.q
        ans = 0
        while b:
            if b & 1:
                ans ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return ans

    def multiply(self, xs) -> int:
        result = 1
        for x in xs:
            result = self.mul_table[result][x]
        return result

    def trace(self, a: int) -> int:
        if self.q == 4:
            value = self.add_table[a][self.mul_table[a][a]]
            assert value in (0, 1)
            return value
        return a


def field_axiom_check(field: Field) -> dict:
    q = field.q
    add, mul = field.add_table, field.mul_table
    comparisons = 0
    for a, b, c in product(range(q), repeat=3):
        assert add[add[a][b]][c] == add[a][add[b][c]]
        assert mul[mul[a][b]][c] == mul[a][mul[b][c]]
        assert mul[a][add[b][c]] == add[mul[a][b]][mul[a][c]]
        comparisons += 3
    for a in range(q):
        assert add[a][0] == a and mul[a][1] == a
        assert add[a][field.neg_table[a]] == 0
        if a:
            assert sum(mul[a][b] == 1 for b in range(q)) == 1
        comparisons += 4 if a else 3
    return {"q": q, "checks": comparisons, "passed": True,
            "construction": "GF(2)[z]/(z^2+z+1)" if q == 4 else "integers modulo q"}


def vector_model(q: int, n: int):
    field = Field(q)
    vectors = [v for v in product(range(q), repeat=2*n) if any(v)]
    add, mul, neg = field.add_table, field.mul_table, field.neg_table
    pairings = []
    for x in vectors:
        row = []
        for y in vectors:
            value = 0
            for j in range(n):
                value = add[value][mul[x[2*j]][y[2*j+1]]]
                value = add[value][neg[mul[x[2*j+1]][y[2*j]]]]
            row.append(value)
        pairings.append(row)
    for i in range(len(vectors)):
        assert pairings[i][i] == 0
        for j in range(len(vectors)):
            assert pairings[i][j] == neg[pairings[j][i]]
    return field, vectors, pairings


def enumerate_labels(pairings, vertices: int, edges):
    size = len(pairings)
    counts = Counter()
    for assignment in product(range(size), repeat=vertices):
        labels = tuple(pairings[assignment[u]][assignment[v]] for u, v in edges)
        counts[labels] += 1
    total = size**vertices
    assert sum(counts.values()) == total
    return counts, total


def edge_probability(q: int, N: int, a: int) -> Fraction:
    return Fraction(N-q if a == 0 else N, q*(N-1))


def independent_probability(q: int, N: int, labels) -> Fraction:
    return prod(edge_probability(q, N, a) for a in labels)


def kappa(q: int, labels) -> int:
    return prod(q-1 if a == 0 else -1 for a in labels)


def balanced_frequency_sum(field: Field, labels) -> int:
    """Proposed closed formula for K, evaluated with actual field arithmetic."""
    q, ell = field.q, len(labels)
    assert ell % 2 == 0
    k = ell // 2
    if 0 in labels:
        numerator = kappa(q, labels)
    else:
        left = field.multiply(labels[::2])
        right = field.multiply(labels[1::2])
        if k % 2:
            right = field.neg_table[right]
        balanced = left == right
        numerator = 1 + q**k * ((q-1)*balanced - 1)
    assert numerator % (q-1) == 0
    return numerator // (q-1)


def cycle_probability(field: Field, n: int, labels) -> Fraction:
    q, ell = field.q, len(labels)
    N, k = q**(2*n), ell//2
    base = independent_probability(q, N, labels)
    kap = kappa(q, labels)
    if ell % 2:
        difference = Fraction(N**(k+1)*kap, q**ell*(N-1)**ell)
    else:
        kval = balanced_frequency_sum(field, labels)
        difference = Fraction(N**k*((N-1)*kval-kap), q**ell*(N-1)**ell)
    return base + difference


def expected_chi_squared(q: int, n: int, ell: int) -> Fraction:
    N = q**(2*n)
    if ell % 2:
        return Fraction((q-1)**ell*N, (N-q)**ell)
    return (q-1)**(ell-2)*(Fraction(1, (N-q)**(ell-2)) +
                           Fraction(q-2, (N-1)**(ell-2)))


def expected_tv(q: int, n: int, ell: int) -> Fraction:
    N, k = q**(2*n), ell//2
    if ell % 2:
        return Fraction(2**(ell-1)*(q-1)**ell*N**(k+1), q**ell*(N-1)**ell)
    numerator = ((N-q)*((q-1)*2**(ell-1)-(q-2)) +
                 (N-1)*(q-2)*q**k)
    return Fraction(N**k*(q-1)**(ell-2)*numerator, q**ell*(N-1)**ell)


def frac_json(x: Fraction) -> dict:
    return {"numerator": x.numerator, "denominator": x.denominator,
            "decimal": float(x)}


def verify_cycle(q: int, n: int, ell: int, model) -> dict:
    field, vectors, pairings = model
    edges = [(i, (i+1) % ell) for i in range(ell)]
    counts, total = enumerate_labels(pairings, ell, edges)
    N = q**(2*n)
    tv, chi_squared = Fraction(0), Fraction(0)
    for labels in product(range(q), repeat=ell):
        observed = Fraction(counts[labels], total)
        predicted = cycle_probability(field, n, labels)
        assert observed == predicted, (q, n, ell, labels, observed, predicted)
        reference = independent_probability(q, N, labels)
        difference = observed-reference
        tv += abs(difference)/2
        chi_squared += difference*difference/reference
    assert tv == expected_tv(q, n, ell), (q, n, ell, tv)
    assert chi_squared == expected_chi_squared(q, n, ell), (q, n, ell, chi_squared)
    # Every proper subset of edges of a simple cycle is a forest.
    marginal_checks = 0
    for mask in range(1, 2**ell-1):
        selected = [i for i in range(ell) if mask >> i & 1]
        marginals = Counter()
        for labels, count in counts.items():
            marginals[tuple(labels[i] for i in selected)] += count
        for labels in product(range(q), repeat=len(selected)):
            observed = Fraction(marginals[labels], total)
            assert observed == independent_probability(q, N, labels)
            marginal_checks += 1
    return {"q": q, "n": n, "ambient_dimension": 2*n, "cycle_length": ell,
            "nonzero_vectors": len(vectors), "vector_assignments": total,
            "label_outcomes_checked": q**ell,
            "proper_edge_subsets_checked": 2**ell-2,
            "proper_marginal_equalities_checked": marginal_checks,
            "total_variation": frac_json(tv), "chi_squared": frac_json(chi_squared),
            "passed": True}


def verify_cactus(q: int, n: int, with_bridge: bool, model) -> dict:
    field, vectors, pairings = model
    edges = [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]
    vertices = 5
    if with_bridge:
        edges.append((2, 5))
        vertices = 6
    counts, total = enumerate_labels(pairings, vertices, edges)
    N = q**(2*n)
    # Checks against the product of the two independently derived cycle laws.
    for labels in product(range(q), repeat=len(edges)):
        predicted = (cycle_probability(field, n, labels[:3]) *
                     cycle_probability(field, n, labels[3:6]))
        if with_bridge:
            predicted *= edge_probability(q, N, labels[6])
        observed = Fraction(counts[labels], total)
        assert observed == predicted, (q, n, with_bridge, labels, observed, predicted)
    return {"q": q, "n": n, "vertices": vertices, "edges": edges,
            "description": "two triangles sharing one vertex" +
                           (", plus a bridge" if with_bridge else ""),
            "vector_assignments": total, "label_outcomes_checked": q**len(edges),
            "passed": True}


def verify_tree(q: int, n: int, model) -> dict:
    field, vectors, pairings = model
    edges = [(0, 1), (2, 0), (2, 3)]
    counts, total = enumerate_labels(pairings, 4, edges)
    N = q**(2*n)
    for labels in product(range(q), repeat=3):
        assert Fraction(counts[labels], total) == independent_probability(q, N, labels)
    return {"q": q, "n": n, "vertices": 4, "edges": edges,
            "vector_assignments": total, "label_outcomes_checked": q**3,
            "passed": True}


def verify_even_character_sum(q: int, ell: int) -> dict:
    """Exact independent evaluation of K using character exponent counts.

    For a primitive p-th root zeta, an integer vector c satisfies
    sum_j c_j zeta^j = K iff c_0-c_{p-1}=K and c_j=c_{p-1} for 0<j<p-1.
    This uses the minimal polynomial 1+X+...+X^(p-1).
    """
    field = Field(q)
    freqs = [t for t in product(range(1, q), repeat=ell)
             if field.multiply(t[::2]) == field.multiply(t[1::2])]
    assert len(freqs) == (q-1)**(ell-1)
    for labels in product(range(q), repeat=ell):
        exponents = [0]*field.p
        for t in freqs:
            exponent = 0
            for ti, ai in zip(t, labels):
                exponent = field.add_table[exponent][field.mul_table[ti][ai]]
            trace = field.trace(field.neg_table[exponent])
            exponents[trace] += 1
        expected = balanced_frequency_sum(field, labels)
        constant = exponents[-1]
        assert exponents[0]-constant == expected
        assert all(x == constant for x in exponents[1:-1])
    return {"q": q, "length": ell, "labels_checked": q**ell,
            "balanced_frequencies": len(freqs), "passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent / "verification.json")
    args = parser.parse_args()
    started = time.perf_counter()
    cycle_cases = ([(2, 1, ell) for ell in range(3, 9)] +
                   [(2, 2, ell) for ell in (3, 4)] +
                   [(3, 1, ell) for ell in (3, 4, 5)] +
                   [(3, 2, 3)] +
                   [(4, 1, ell) for ell in (3, 4)] +
                   [(5, 1, ell) for ell in (3, 4)])
    model_keys = sorted({(q, n) for q, n, _ in cycle_cases})
    models = {(q, n): vector_model(q, n) for q, n in model_keys}
    results = {"description": "Independent exhaustive enumeration of actual nonzero vectors",
               "python": platform.python_version(), "arithmetic": "exact integers and Fraction",
               "fields": [field_axiom_check(Field(q)) for q in (2, 3, 4, 5)],
               "cycles": [], "cacti": [], "trees": [], "even_character_sums": []}
    for q, n, ell in cycle_cases:
        result = verify_cycle(q, n, ell, models[q, n])
        results["cycles"].append(result)
        print(f"PASS cycle q={q}, n={n}, length={ell}, assignments={result['vector_assignments']}", flush=True)
    for q, n, bridge in [(2, 1, False), (2, 1, True), (3, 1, False), (3, 1, True)]:
        result = verify_cactus(q, n, bridge, models[q, n])
        results["cacti"].append(result)
        print(f"PASS cactus q={q}, n={n}, bridge={bridge}, assignments={result['vector_assignments']}", flush=True)
    for q, n in [(2, 1), (2, 2), (3, 1), (4, 1), (5, 1)]:
        result = verify_tree(q, n, models[q, n])
        results["trees"].append(result)
        print(f"PASS tree q={q}, n={n}, assignments={result['vector_assignments']}", flush=True)
    for q, ell in [(2, 4), (2, 6), (3, 4), (3, 6), (4, 4), (5, 4)]:
        result = verify_even_character_sum(q, ell)
        results["even_character_sums"].append(result)
        print(f"PASS even character sum q={q}, length={ell}", flush=True)
    results["summary"] = {
        "all_passed": True,
        "cycle_cases": len(results["cycles"]),
        "cactus_cases": len(results["cacti"]),
        "tree_cases": len(results["trees"]),
        "even_character_sum_cases": len(results["even_character_sums"]),
        "actual_vector_assignments_enumerated": sum(
            r["vector_assignments"] for key in ("cycles", "cacti", "trees") for r in results[key]),
        "cycle_label_outcomes_checked": sum(r["label_outcomes_checked"] for r in results["cycles"]),
        "proper_cycle_edge_subsets_checked": sum(r["proper_edge_subsets_checked"] for r in results["cycles"]),
        "proper_cycle_marginal_equalities_checked": sum(r["proper_marginal_equalities_checked"] for r in results["cycles"]),
        "elapsed_seconds": round(time.perf_counter()-started, 6),
        "scope": "Finite computations verify the formulas in these cases; the universal theorems rely on the proofs."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results["summary"], indent=2), flush=True)


if __name__ == "__main__":
    main()
