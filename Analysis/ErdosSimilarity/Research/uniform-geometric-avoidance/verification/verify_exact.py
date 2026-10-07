#!/usr/bin/env python3
"""Exact finite checks accompanying Uniform geometric avoidance.

Run with Python 3.10+; the standard library suffices.  This program checks
finite arithmetic instances and exhaustive finite probability spaces.  It is
not a formalization of the theorem or a construction of its infinite set.
See README.md for the precise scope and the intentional negative control.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path


class Checks:
    def __init__(self):
        self.counts = Counter()

    def require(self, category, condition, explanation=""):
        if not condition:
            raise RuntimeError(f"FAILED [{category}]: {explanation}")
        self.counts[category] += 1


V = Checks()


def rational_string(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else str(value)


def rational_samples(alpha, beta, max_denominator=18):
    return sorted({alpha, beta} | {
        F(a, b) for b in range(2, max_denominator + 1)
        for a in range(1, b) if alpha <= F(a, b) <= beta
    })


def exponent_bound(beta, Q):
    T, power = 1, beta
    while power > Q:
        T, power = T + 1, power * beta
    return T


@lru_cache(maxsize=None)
def selected(q, Q, j):
    """Return the least nu >= 1 with q**nu <= Q**j, without logarithms."""
    threshold = Q ** j
    lo, hi = 0, 1
    while q ** hi > threshold:
        hi *= 2
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if q ** mid <= threshold:
            hi = mid
        else:
            lo = mid
    return hi, q ** hi


def check_synchronization():
    reports = []
    for alpha, beta, Q in [(F(1, 4), F(3, 4), F(1, 16)),
                           (F(1, 8), F(7, 8), F(1, 32)),
                           (F(1, 3), F(2, 3), F(1, 16))]:
        qs = rational_samples(alpha, beta)
        T = exponent_bound(beta, Q)
        exponents = {}
        for q in qs:
            previous_n, previous_a = 0, F(1)
            for j in range(1, 25):
                n, a = selected(q, Q, j)
                V.require("synchronization", q ** (n - 1) > Q ** j >= a)
                V.require("synchronization", alpha * Q ** j < a <= Q ** j)
                V.require("synchronization", n <= T * j and n > previous_n)
                if j > 1:
                    V.require("synchronization", previous_a - a >= (alpha - Q) * Q ** (j - 1))
                exponents[q, j] = n
                previous_n, previous_a = n, a
        for j in range(1, 25):
            V.require("synchronization", all(exponents[q, j] <= exponents[q2, j]
                                             for q, q2 in zip(qs, qs[1:])))
        reports.append({"alpha": str(alpha), "beta": str(beta), "Q": str(Q),
                        "T": T, "rational_ratios": len(qs), "levels_per_ratio": 24})

    # Equality is assigned to the smaller exponent; the right-hand jump must
    # be represented separately in the parameter-stratification argument.
    Q, q0, delta = F(1, 16), F(1, 2), F(1, 2 ** 20)
    for j in range(1, 25):
        triple = [selected(q, Q, j)[0] for q in (q0 - delta, q0, q0 + delta)]
        V.require("jump_boundaries", triple == [4 * j, 4 * j, 4 * j + 1])
        V.require("jump_boundaries", selected(q0, Q, j)[1] == Q ** j)
    return {"bands": reports, "exact_jump_levels": 24}


def check_mixtures():
    alpha, beta, Q = F(1, 4), F(3, 4), F(1, 16)
    T = exponent_bound(beta, Q)
    mixtures = [((F(1),), (F(1, 2),)),
                ((F(1, 2), F(1, 2)), (alpha, beta)),
                ((F(1, 3), F(2, 3)), (F(1, 3), F(2, 3))),
                ((F(0), F(2, 5), F(3, 5)), (alpha, F(1, 2), beta)),
                ((F(1, 7), F(2, 7), F(4, 7)), (F(1, 2), F(1, 2), beta))]
    for weights, bases in mixtures:
        V.require("mixture_synchronization", sum(weights) == 1 and min(weights) >= 0)
        n, powers, previous_a, previous_n = 0, [F(1)] * len(bases), F(1), 0
        for j in range(1, 25):
            value = sum(w * a for w, a in zip(weights, powers))
            preceding = None
            while value > Q ** j:
                preceding = value
                powers = [a * q for a, q in zip(powers, bases)]
                n += 1
                value = sum(w * a for w, a in zip(weights, powers))
                V.require("mixture_synchronization", alpha * preceding <= value <= beta * preceding)
            V.require("mixture_synchronization", preceding is not None and preceding > Q ** j)
            V.require("mixture_synchronization", alpha * Q ** j < value <= Q ** j)
            V.require("mixture_synchronization", previous_n < n <= T * j)
            if j > 1:
                V.require("mixture_synchronization", previous_a - value >= (alpha - Q) * Q ** (j - 1))
            previous_a, previous_n = value, n
    return {"normalized_mixtures": len(mixtures), "levels_per_mixture": 24,
            "degeneracies_included": ["zero coefficient", "repeated base"]}


@dataclass(frozen=True)
class Edge:
    path: tuple
    height: int
    a: int
    b: int


def make_windows(M, d, g, r0, j0):
    lengths, spans = {1: r0}, {1: M * r0 + (M - 1) * g}
    for h in range(2, d + 1):
        lengths[h] = g + spans[h - 1]
        spans[h] = M * (lengths[h] + g + spans[h - 1]) + (M - 1) * g
    edges = []
    cursor = j0

    def visit(h, path):
        nonlocal cursor
        for child in range(1, M + 1):
            edge = Edge(path + (child,), h, cursor, cursor + lengths[h] - 1)
            edges.append(edge)
            cursor = edge.b + g + 1
            if h > 1:
                visit(h - 1, edge.path)

    visit(d, ())
    return edges, lengths, spans


def block_indices(edges, edge):
    return [i for i, f in enumerate(edges) if f.path[:len(edge.path)] == edge.path]


def check_windows():
    cases, edge_instances = 0, 0
    for M, d, g, r0, j0 in product((2, 3, 4), (1, 2, 3), (1, 2, 5), (1, 2, 7), (1, 3)):
        edges, lengths, spans = make_windows(M, d, g, r0, j0)
        cases += 1
        edge_instances += len(edges)
        V.require("preorder_windows", len(edges) == sum(M ** h for h in range(1, d + 1)))
        V.require("preorder_windows", all(f.a - e.b == g + 1 for e, f in zip(edges, edges[1:])))
        V.require("preorder_windows", edges[-1].b == j0 - 1 + spans[d])
        A = M * (2 * M) ** (d - 1)
        G = (M - 1) * (2 * M) ** (d - 1) + F((3 * M - 1) * ((2 * M) ** (d - 1) - 1), 2 * M - 1)
        V.require("affine_endpoint", G.denominator == 1)
        V.require("affine_endpoint", edges[-1].b == j0 - 1 + A * r0 + G * g)
        for e in edges:
            indices = block_indices(edges, e)
            V.require("preorder_windows", indices == list(range(indices[0], indices[-1] + 1)))
            span = edges[indices[-1]].b - e.a + 1
            V.require("preorder_windows", span <= 2 * lengths[e.height])
            V.require("preorder_windows", span == (lengths[1] if e.height == 1 else 2 * lengths[e.height]))
    return {"parameter_cases": cases, "edge_instances": edge_instances,
            "M_values": [2, 3, 4], "height_values": [1, 2, 3]}


@lru_cache(maxsize=None)
def grid_size(b, alpha=F(1, 4), Q=F(1, 16)):
    target = 4 / (alpha - Q) * Q ** (-b)
    N = 1 << max(0, target.numerator.bit_length() - target.denominator.bit_length())
    while N * target.denominator < target.numerator:
        N <<= 1
    return N


def key(N, z):
    Nz = N * z
    return (Nz.numerator // Nz.denominator) % N


def stable_at_grid(x, shift, N):
    Nx = N * x
    next_boundary_index = Nx.numerator // Nx.denominator + 1
    return N * (x + shift) < next_boundary_index


def check_grids():
    alpha, beta, Q = F(1, 4), F(3, 4), F(1, 16)
    c = 4 / (alpha - Q)
    for b in range(1, 81):
        N = grid_size(b)
        V.require("dyadic_grids", N & (N - 1) == 0)
        V.require("dyadic_grids", c * Q ** (-b) <= N < 2 * c * Q ** (-b))
        if b > 1:
            V.require("dyadic_grids", N % grid_size(b - 1) == 0)
        for z in (F(0), F(1, 3), F(-1, 7), F(17, 16)):
            V.require("dyadic_grids", key(N, z) == key(N, z + 2))
            if b > 1:
                V.require("dyadic_grids", key(grid_size(b - 1), z) == key(N, z) // (N // grid_size(b - 1)))

    edges, _, _ = make_windows(2, 2, 3, 2, 1)
    qs, scales, centers = rational_samples(alpha, beta, 12), (F(1), F(3, 2), F(2)), (F(0), F(1, 3), F(-1, 7), F(17, 16))
    stable_centers = [x for x in centers if all(stable_at_grid(x, 2 * Q ** e.a, grid_size(edges[k - 1].b))
                                               for k, e in enumerate(edges) if k)]
    V.require("stable_keys", len(stable_centers) == len(centers))
    point_configurations = 0
    for q, t, x, e in product(qs, scales, centers, edges):
        point_configurations += 1
        points = [x] + [x + t * selected(q, Q, j)[1] for j in range(e.a, e.b + 1)]
        N, finest = grid_size(e.b), grid_size(edges[block_indices(edges, e)[-1]].b)
        V.require("grid_separation", max(points) - min(points) <= F(1, 4))
        V.require("grid_separation", len({key(N, z) for z in points}) == len(points))
        V.require("grid_separation", len({key(finest, z) for z in points}) == len(points))
        for z, z2 in combinations(points, 2):
            distance = abs(z - z2)
            V.require("grid_separation", distance >= (alpha - Q) * Q ** e.b > F(1, N))
        for earlier in edges[:edges.index(e)]:
            for z in points[1:]:
                V.require("stable_keys", key(grid_size(earlier.b), z) == key(grid_size(earlier.b), x))

    boundary_cases = 0
    for k, e in enumerate(edges):
        if not k:
            continue
        N, shift = grid_size(edges[k - 1].b), 2 * Q ** e.a
        V.require("half_open_boundaries", 2 * shift < F(1, N))
        # x itself is excluded, but an arrival exactly at a boundary counts.
        for x, expected in [(F(0), True), (-shift, False), (-3 * shift / 2, True), (-shift / 2, False)]:
            boundary_cases += 1
            V.require("half_open_boundaries", stable_at_grid(x, shift, N) == expected)
            V.require("half_open_boundaries", (key(N, x) == key(N, x + shift)) == expected)
        V.require("stability_density", 2 * N * Q ** e.a <= 4 * c * Q ** 4)
    return {"grid_levels": 80, "rational_ratios": len(qs), "point_configurations": point_configurations,
            "stable_centers": len(stable_centers), "half_open_boundary_cases": boundary_cases,
            "sample_window_endpoint": edges[-1].b}


def probability_from_counts(counts, terminal_entries, selector_states, p):
    return sum(F(count) * p ** ones * (1 - p) ** (terminal_entries - ones)
               for ones, count in enumerate(counts)) / selector_states


def enumerate_routing_model(name, test_count, terminal_entries, selector_states):
    """Exhaust every selector state and every potential terminal assignment."""
    counts = [[0] * (terminal_entries + 1) for _ in range(1 << test_count)]
    for gates, addresses in selector_states:
        V.require("adaptive_terminal_addresses", len(set(addresses)) == test_count)
        for terminal_mask in range(1 << terminal_entries):
            pattern = sum(1 << j for j in range(test_count)
                          if (gates >> j) & 1 and (terminal_mask >> addresses[j]) & 1)
            counts[pattern][terminal_mask.bit_count()] += 1
    states = len(selector_states) * (1 << terminal_entries)
    V.require("exhaustive_routing", sum(map(sum, counts)) == states)
    reports = []
    for p in (F(1, 3), F(2, 5), F(1, 2)):
        probabilities = [probability_from_counts(row, terminal_entries, len(selector_states), p) for row in counts]
        for pattern, actual in enumerate(probabilities):
            ones = pattern.bit_count()
            target = (p / 2) ** ones * (1 - p / 2) ** (test_count - ones)
            V.require("exhaustive_routing", actual == target)
        V.require("exhaustive_routing", sum(probabilities) == 1)
        reports.append({"p": str(p), "failure_probability": rational_string(probabilities[0]),
                        "target": rational_string((1 - p / 2) ** test_count)})
    return {"model": name, "test_count": test_count, "selector_states": len(selector_states),
            "terminal_entries": terminal_entries, "complete_assignments": states,
            "joint_outcome_patterns_checked_per_p": 1 << test_count, "probabilities": reports}


def check_routing():
    # Two distinct test points, each with an independent subtree selector.
    geometric_states = [(gates, tuple(((route >> j) & 1) * 2 + j for j in range(2)))
                        for gates, route in product(range(4), repeat=2)]
    reports = [enumerate_routing_model("two-point geometric address pattern", 2, 4, geometric_states)]

    # Stress test: two local child subtrees, each holding two points. Both
    # points share a subtree selector; their selected leaves also depend on
    # the other point's gate. This deliberately permits more selector
    # dependence than the grid construction needs. Keys j still separate
    # terminal addresses within a leaf. Center entries are fixed and do not
    # alias the unexposed gates, as required after conditioning on F_x.
    shared_states = []
    for gates, shared in product(range(16), range(4)):
        addresses = []
        for index in range(4):
            subtree, j = divmod(index, 2)
            shared_bit = (shared >> subtree) & 1
            other_gate = (gates >> (2 * subtree + 1 - j)) & 1
            leaf = (shared_bit + other_gate + j) % 3
            addresses.append((subtree * 3 + leaf) * 2 + j)
        shared_states.append((gates, tuple(addresses)))
    reports.append(enumerate_routing_model("shared and gate-dependent subtree selectors", 4, 12, shared_states))

    controls = []
    for p in (F(1, 3), F(2, 5), F(1, 2)):
        actual = F(0)
        for gates, terminal in product(range(4), range(2)):
            if terminal == 0 or gates == 0:
                actual += (p if terminal else 1 - p) / 4
        target = (1 - p / 2) ** 2
        V.require("shared_terminal_negative_control", actual == 1 - 3 * p / 4)
        V.require("shared_terminal_negative_control", actual - target == p * (1 - p) / 4 > 0)
        controls.append({"p": str(p), "shared_terminal_failure": str(actual),
                         "independent_terminal_target": str(target), "gap": str(actual - target)})
    return {"models": reports, "negative_control": controls,
            "negative_control_meaning": "Aliasing terminal addresses breaks the identity; this failure is expected."}


def check_no_default():
    reports = []
    for M, d in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 2)):
        nodes = [()]
        for depth in range(1, d):
            nodes.extend(product(range(M), repeat=depth))
        indices = {node: i * (M - 1) for i, node in enumerate(nodes)}
        bits = len(nodes) * (M - 1)
        distribution = Counter()
        for mask in range(1 << bits):
            path, first_default = (), None
            for depth in range(d):
                child = M - 1
                for i in range(M - 1):
                    if (mask >> (indices[path] + i)) & 1:
                        child = i
                        break
                if child == M - 1 and first_default is None:
                    first_default = depth
                path += (child,)
            distribution[first_default] += 1
        delta = F(1, 2 ** (M - 1))
        V.require("no_default_distribution", F(distribution[None], 1 << bits) == (1 - delta) ** d)
        for depth in range(d):
            V.require("no_default_distribution", F(distribution[depth], 1 << bits) == (1 - delta) ** depth * delta)
        reports.append({"M": M, "height": d, "center_selector_assignments": 1 << bits,
                        "no_default_probability": str(F(distribution[None], 1 << bits))})
    return reports


def interval_union_measure(intervals):
    total, left, right = F(0), None, None
    for a, b in sorted(intervals):
        if b <= a:
            continue
        if left is None:
            left, right = a, b
        elif a > right:
            total += right - left
            left, right = a, b
        else:
            right = max(right, b)
    return total + (right - left if left is not None else 0)


def check_periodic_assembly():
    budget_cases = 0
    for eta, M, K in product((F(1, 10), F(1, 3), F(1, 2), F(1)), range(1, 9), range(8)):
        partial = sum(eta * F(1, 24 * 2 ** m * 2 ** (k + 1)) for m in range(1, M + 1) for k in range(K + 1))
        mass = eta / 2
        a, b = F(1, 2 ** M), F(1, 2 ** (K + 1))
        V.require("periodic_budgets", 12 * partial == mass * (1 - a) * (1 - b))
        V.require("periodic_budgets", mass - 12 * partial == mass * (a + b - a * b))
        V.require("periodic_budgets", mass - 12 * partial <= mass * (a + b))
        budget_cases += 1

    interval_families = [((F(0), F(1, 9)), (F(1, 4), F(2, 5)), (F(7, 8), F(1))),
                         ((F(1, 10), F(1, 3)), (F(1, 4), F(1, 2)), (F(3, 4), F(7, 8)))]
    transformations = 0
    for intervals, k, sign in product(interval_families, range(7), (-1, 1)):
        scale = 2 ** k
        reflected = intervals if sign == 1 else tuple((1 - b, 1 - a) for a, b in intervals)
        copies = [((a + j) / scale, (b + j) / scale) for j in range(scale) for a, b in reflected]
        V.require("periodic_density", interval_union_measure(copies) == interval_union_measure(intervals))
        transformations += 1
    for intervals, start in product(interval_families, (F(1, 3), F(-7, 11), F(5, 2))):
        floor = start.numerator // start.denominator
        pieces = [(max(start, a + j), min(start + 1, b + j))
                  for a, b in intervals for j in range(floor - 1, floor + 3)]
        V.require("periodic_density", interval_union_measure(pieces) == interval_union_measure(intervals))

    scale_cases = 0
    qs = rational_samples(F(1, 4), F(3, 4), 12)
    for q, magnitude, sign in product(qs, (F(1, 1000), F(1, 3), F(1, 2), F(1), F(4, 3), F(5), F(128)), (-1, 1)):
        h, w = 0, magnitude
        while w > 1:
            h, w = h + 1, w * q
        k, t = 0, w
        while t < 1:
            k, t = k + 1, 2 * t
        V.require("scale_normalization", k >= 0 and 1 <= t < 2 and magnitude * q ** h == F(1, 2 ** k) * t)
        for x, n in product((F(0), F(1, 3), F(-2)), (1, 2, 4)):
            transformed = sign * F(1, 2 ** k) * (sign * 2 ** k * x + t * q ** n)
            V.require("scale_normalization", transformed == x + sign * magnitude * q ** (h + n))
        scale_cases += 1
    return {"budget_cases": budget_cases, "signed_contraction_density_cases": transformations,
            "signed_scale_normalizations": scale_cases,
            "full_signed_density_budget": "eta/2",
            "exact_rectangular_tail": "(eta/2)*(2^-M+2^-(K+1)-2^-(M+K+1))",
            "tail_majorant": "(eta/2)*(2^-M+2^-(K+1))"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    results = {"status": "passed", "arithmetic": "Python fractions.Fraction and arbitrary-precision integers; no floating point",
               "scope": "Exact finite checks only; neither an infinite-set construction nor a formal theorem proof",
               "synchronization": check_synchronization(),
               "positive_mixtures": check_mixtures(),
               "windows": check_windows(),
               "grids": check_grids(),
               "conditional_routing": check_routing(),
               "no_default": check_no_default(),
               "periodic_assembly": check_periodic_assembly()}
    results["checks_by_category"] = dict(sorted(V.counts.items()))
    results["total_exact_checks"] = sum(V.counts.values())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"PASS: {results['total_exact_checks']:,} exact checks; results written to {args.output}")


if __name__ == "__main__":
    main()
