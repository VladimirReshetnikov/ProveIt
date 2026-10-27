#!/usr/bin/env python3
"""Exact reference primitive for deterministic high-moment edge packing.

This implementation is intended for small reproducible instances.  Its exact
conditional-moment computation enumerates ordered tuples of at most 2*k edges;
the proof, not a timing experiment, justifies the quasipolynomial cost when
k is proportional to log of an asymptotic root size.  Parallel edges are kept
as distinct positions in the input list.

No floating point operations or random choices occur in the algorithm.
Only Python's standard library is required.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb
from typing import Dict, Hashable, List, Mapping, Sequence, Tuple


Edge = Tuple[Hashable, Hashable]
Vertex = Tuple[str, Hashable]
Labels = Dict[Vertex, int]


def vertices(edges: Sequence[Edge]) -> List[Vertex]:
    """Return the bipartite vertices in deterministic first-occurrence order."""
    answer: List[Vertex] = []
    seen = set()
    for left, right in edges:
        for vertex in (("L", left), ("R", right)):
            if vertex not in seen:
                seen.add(vertex)
                answer.append(vertex)
    return answer


def degrees(edges: Sequence[Edge]) -> Counter:
    return Counter(vertex for left, right in edges
                   for vertex in (("L", left), ("R", right)))


def matching_partition(edges: Sequence[Edge]) -> List[List[int]]:
    """Greedily partition a multigraph's edge positions into matchings."""
    classes: List[List[int]] = []
    occupied: List[set] = []
    for index, (left, right) in enumerate(edges):
        endpoints = {("L", left), ("R", right)}
        for positions, used in zip(classes, occupied):
            if endpoints.isdisjoint(used):
                positions.append(index)
                used.update(endpoints)
                break
        else:
            classes.append([index])
            occupied.append(set(endpoints))
    return classes


def loads(edges: Sequence[Edge], label_count: int,
          labels: Mapping[Vertex, int]) -> List[int]:
    answer = [0] * (label_count * label_count)
    for left, right in edges:
        a = labels[("L", left)]
        b = labels[("R", right)]
        if not (0 <= a < label_count and 0 <= b < label_count):
            raise ValueError("A vertex label is outside the allowed range")
        answer[a * label_count + b] += 1
    return answer


def potential_from_loads(values: Sequence[int], edge_count: int,
                         label_count: int, moment_half: int) -> Fraction:
    center = Fraction(edge_count, label_count * label_count)
    return sum(((Fraction(value) - center) ** (2 * moment_half)
                for value in values), Fraction(0))


def conditional_potential(edges: Sequence[Edge], label_count: int,
                          moment_half: int,
                          assigned: Mapping[Vertex, int]) -> Fraction:
    """Compute E[sum_gamma (X_gamma - M/R^2)^(2*k) | assigned].

    Expansion is over ordered tuples of edge positions, so repeated and
    parallel edges are handled exactly.  Every term has denominator dividing
    R^(4*k).  The running time is R^2 * (M+1)^O(k), and the enumeration stores
    only one edge tuple and its endpoint set at a time.
    """
    if label_count < 1 or moment_half < 1:
        raise ValueError("label_count and moment_half must be positive")
    if any(not (0 <= value < label_count) for value in assigned.values()):
        raise ValueError("A vertex label is outside the allowed range")
    m = len(edges)
    q = 2 * moment_half
    tagged = [(("L", left), ("R", right)) for left, right in edges]
    r_powers = [label_count ** exponent for exponent in range(2 * q + 1)]
    numerator = 0
    for a, b in product(range(label_count), repeat=2):
        for j in range(q + 1):
            coefficient = comb(q, j) * (-m) ** (q - j)
            if coefficient == 0:
                continue
            subtotal = 0
            for edge_indices in product(range(m), repeat=j):
                endpoints = set()
                for index in edge_indices:
                    endpoints.update(tagged[index])
                unassigned = 0
                consistent = True
                for vertex in endpoints:
                    required = a if vertex[0] == "L" else b
                    if vertex in assigned:
                        if assigned[vertex] != required:
                            consistent = False
                            break
                    else:
                        unassigned += 1
                if consistent:
                    # R^(4k) * (M/R^2)^(2k-j) * R^(-unassigned)
                    # leaves the integer power R^(2j-unassigned).
                    subtotal += r_powers[2 * j - unassigned]
            numerator += coefficient * subtotal
    if numerator < 0:
        raise ArithmeticError("A nonnegative moment potential became negative")
    return Fraction(numerator, r_powers[2 * q])


def deterministic_pack(edges: Sequence[Edge], label_count: int,
                       moment_half: int) -> dict:
    """Assign labels by exact conditional expectation; return an audit trace."""
    assigned: Labels = {}
    current = conditional_potential(edges, label_count, moment_half, assigned)
    initial = current
    trace = []
    for vertex in vertices(edges):
        alternatives = []
        for label in range(label_count):
            trial = dict(assigned)
            trial[vertex] = label
            alternatives.append(conditional_potential(
                edges, label_count, moment_half, trial))
        average = sum(alternatives, Fraction(0)) / label_count
        if average != current:
            raise ArithmeticError("The conditional-expectation averaging identity failed")
        chosen = min(range(label_count), key=lambda value: (alternatives[value], value))
        next_value = alternatives[chosen]
        if next_value > current:
            raise ArithmeticError("The conditional-expectation potential increased")
        trace.append({"vertex": vertex, "before": current,
                      "alternatives": alternatives, "chosen": chosen,
                      "after": next_value})
        assigned[vertex] = chosen
        current = next_value
    result_loads = loads(edges, label_count, assigned)
    actual = potential_from_loads(result_loads, len(edges), label_count, moment_half)
    if actual != current:
        raise ArithmeticError("The final potential disagrees with the actual loads")
    return {"labels": assigned, "loads": result_loads,
            "initial_potential": initial, "final_potential": actual,
            "trace": trace}


def proved_potential_bound(edges: Sequence[Edge], label_count: int,
                           moment_half: int) -> Fraction:
    """Rational upper bound D * [4 max(sqrt(k*K*mu), k*K)]^(2*k)."""
    if not edges:
        return Fraction(0)
    k = moment_half
    matching_count = len(matching_partition(edges))
    d = label_count * label_count
    mu = Fraction(len(edges), d)
    return (d * 4 ** (2 * k)
            * max((k * matching_count * mu) ** k,
                  Fraction((k * matching_count) ** (2 * k))))


def second_moment_formula(edges: Sequence[Edge], label_count: int) -> Fraction:
    """Exact total second moment from ordered edge-pair intersection types."""
    multiplicities = Counter(edges)
    parallel_pairs = sum(value * value for value in multiplicities.values())
    degree_square_sum = sum(value * value for value in degrees(edges).values())
    share_one_pairs = degree_square_sum - 2 * parallel_pairs
    r = label_count
    return (parallel_pairs * (1 - Fraction(1, r * r))
            + share_one_pairs * (Fraction(1, r) - Fraction(1, r * r)))
