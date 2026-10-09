#!/usr/bin/env python3
"""Independent exact checks for weighted closed tree walks.

The recurrence is checked against direct first-appearance walk enumeration.
All counted values and identities are exact integers or fractions.  These
finite checks are not a proof of an asymptotic error estimate.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
import time


def weighted_rows(order: int, numerator: int = 1, denominator: int = 1):
    """Return denominator**k * F[k,m](numerator/denominator).

    Scaling by half-length gives an integer recurrence even for rational c.
    The extra factor at a root edge used q times is p * denominator**(q-1).
    """
    rows = [[1]]
    cuts = [[1] * (order + 1)]
    powers = [denominator**q for q in range(order + 1)]
    choose = [[comb(n, j) for j in range(n + 1)] for n in range(order + 1)]
    for k in range(1, order + 1):
        row = [0] * (k + 1)
        for m in range(1, k + 1):
            value = numerator * powers[m - 1] * cuts[k - m][m]
            for q in range(1, m):
                convolution = sum(
                    cuts[a][q] * rows[k - q - a][m - q]
                    for a in range(k - m + 1)
                )
                value += numerator * powers[q - 1] * choose[m - 1][q - 1] * convolution
            row[m] = value
        rows.append(row)
        cuts.append([
            0 if q == 0 else sum(row[ell] * comb(ell + q - 1, ell)
                                for ell in range(1, k + 1))
            for q in range(order - k + 1)
        ])
    return rows, cuts


def enumerate_walks(k: int):
    """Generate normalized walks directly, without the recurrence or partitions.

    Returns counters keyed by (root departures, edge count), (deficit, edges),
    and (root departures, edges) for walks simple off the root.
    """
    rows, deficits, simple = Counter(), Counter(), Counter()
    adjacency = [[]]
    departures = [0]
    edge_uses = []

    def visit(position: int, vertex: int, depth: int):
        remaining = 2 * k - position
        if remaining < depth or (remaining - depth) % 2:
            return
        if remaining == 0:
            if vertex != 0:
                return
            edges = len(edge_uses)
            rows[departures[0], edges] += 1
            deficits[k - max(departures), edges] += 1
            if all(count == 2 or 0 in endpoints
                   for endpoints, count in edge_uses):
                simple[departures[0], edges] += 1
            return
        # Existing neighbors have already been assigned first-appearance names.
        for neighbor, edge, child in tuple(adjacency[vertex]):
            next_depth = depth + (1 if child else -1)
            departures[vertex] += 1
            edge_uses[edge][1] += 1
            visit(position + 1, neighbor, next_depth)
            edge_uses[edge][1] -= 1
            departures[vertex] -= 1
        # Discovery of exactly the next fresh vertex; no arbitrary labels.
        if remaining >= depth + 2:
            neighbor, edge = len(adjacency), len(edge_uses)
            adjacency.append([(vertex, edge, False)])
            adjacency[vertex].append((neighbor, edge, True))
            departures.append(0)
            edge_uses.append([[vertex, neighbor], 1])
            departures[vertex] += 1
            visit(position + 1, neighbor, depth + 1)
            departures[vertex] -= 1
            edge_uses.pop()
            departures.pop()
            adjacency[vertex].pop()
            adjacency.pop()

    if k:
        visit(0, 0, 0)
    return rows, deficits, simple


def touchard_values(order: int, c: Fraction):
    values = [Fraction(1)]
    for n in range(order):
        values.append(c * sum(comb(n, j) * values[j] for j in range(n + 1)))
    return values


def catalan_forest(n: int, s: int):
    return Fraction(n * comb(n + 2 * s, s), n + 2 * s)


def run(order: int, enumerate_through: int, destination: Path):
    started = time.perf_counter()
    destination.mkdir(parents=True, exist_ok=True)
    parameters = [Fraction(1, 2), Fraction(1), Fraction(2)]
    generated = {}
    for c in parameters:
        rows, cuts = weighted_rows(order, c.numerator, c.denominator)
        generated[c] = rows, cuts
    brute = {k: enumerate_walks(k) for k in range(1, enumerate_through + 1)}
    stirling = [[1]]
    for n in range(1, enumerate_through + 1):
        previous = stirling[-1]
        stirling.append([0] + [
            previous[j-1] + (j*previous[j] if j < n else 0)
            for j in range(1, n+1)
        ])
    coefficient_checks = 0
    for k, (counts, deficits, simple) in brute.items():
        for n in range(1, k+1):
            s = k-n
            forest = catalan_forest(n, s)
            for edges in range(k+1):
                j = edges-s
                expected = forest*stirling[n][j] if 0 <= j <= n else 0
                assert simple[n, edges] == expected
                coefficient_checks += 1
    recurrence_checks = simple_checks = fresh_checks = rotation_checks = 0
    for c in parameters:
        rows, cuts = generated[c]
        touchard = touchard_values(order + 1, c)
        for k, (counts, deficits, simple) in brute.items():
            for m in range(1, k + 1):
                exact = sum(count * c**edges for (root, edges), count in counts.items()
                            if root == m)
                assert exact == Fraction(rows[k][m], c.denominator**k)
                recurrence_checks += 1
                s = k - m
                exact_simple = sum(count * c**edges
                                   for (root, edges), count in simple.items() if root == m)
                expected_simple = touchard[m] * c**s * catalan_forest(m, s)
                assert exact_simple == expected_simple
                simple_checks += 1
            # Weighted rotation identity with I={all departure counts}: each
            # walk contributes its number of vertices, including periodic walks.
            lhs = sum(Fraction(2*k, m) * Fraction(rows[k][m], c.denominator**k)
                      for m in range(1, k + 1))
            rhs = sum(count * c**edges * (edges + 1)
                      for (root, edges), count in counts.items())
            assert lhs == rhs
            rotation_checks += 1
        for k in range(2, order + 1):
            H = sum(comb(k, s) * c**s * touchard[k-s] for s in range(k + 1))
            p = [Fraction(comb(k, s)) * c**s * touchard[k-s] / H
                 for s in range(k + 1)]
            assert sum(p) == 1
            for h in range(1, min(4, k) + 1):
                lhs = sum(Fraction(factorial(s), factorial(s-h)) * p[s]
                          for s in range(h, k + 1))
                Hprev = sum(comb(k-h, s) * c**s * touchard[k-h-s]
                            for s in range(k-h+1))
                rhs = Fraction(factorial(k), factorial(k-h)) * c**h * Hprev / H
                assert lhs == rhs
                fresh_checks += 1
    known = [1, 3, 12, 57, 303, 1747, 10727, 69331, 467963, 3280353,
             23785699, 177877932, 1368977132]
    moments = [sum(row) for row in generated[Fraction(1)][0]][1:]
    assert moments[:min(order, len(known))] == known[:min(order, len(known))]
    tables = {}
    for c in parameters:
        rows = generated[c][0]
        tables[str(c)] = {
            "scaled_moments": [str(sum(row)) for row in rows],
            "row_scale": f"{c.denominator}**k",
            "rows": [[str(x) for x in row] for row in rows],
        }
    (destination / "exact_rows.json").write_text(json.dumps(tables, indent=2) + "\n")
    result = {
        "status": "PASS", "maximum_recurrence_half_length": order,
        "direct_enumeration_through": enumerate_through,
        "enumerated_walks": sum(sum(x[0].values()) for x in brute.values()),
        "weighted_return_row_equalities": recurrence_checks,
        "weighted_simple_forest_equalities": simple_checks,
        "coefficientwise_simple_forest_equalities": coefficient_checks,
        "weighted_rotation_equalities": rotation_checks,
        "fresh_factorial_moment_equalities": fresh_checks,
        "oeis_prefix_terms": min(order, len(known)),
        "parameters": [str(c) for c in parameters],
        "elapsed_seconds": round(time.perf_counter() - started, 3),
        "scope": "Exact finite checks; not verification of asymptotic limits or bounds.",
    }
    (destination / "exact_checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, default=40)
    parser.add_argument("--enumerate-through", type=int, default=7)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    run(args.order, args.enumerate_through, args.output)
