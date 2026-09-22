#!/usr/bin/env python3
"""Finite exact checks for the single-loss linearization manuscript.

Python 3.10+, standard library only. These checks do NOT prove the
infinite analytic theorem, Hahn summability, or bibliographic novelty.
All arithmetic is rational; no numerical inference about an irrational
small-divisor limsup is made.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path


def compositions(total: int, parts: int):
    if parts == 0:
        if total == 0:
            yield ()
        return
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for tail in compositions(total - first, parts - 1):
            yield (first,) + tail


@lru_cache(None)
def trees(size: int) -> tuple:
    """Plane rooted internal skeletons; each node is its child tuple."""
    if size == 1:
        return ((),)
    result = []
    for degree in range(1, size):
        for sizes in compositions(size - 1, degree):
            for children in itertools.product(*(trees(s) for s in sizes)):
                result.append(children)
    return tuple(result)


def tree_data(tree: tuple, weights: tuple[int, ...]):
    degrees, subweights, parent = [], [], []
    cursor = 0
    def visit(node, par):
        nonlocal cursor
        i = cursor
        cursor += 1
        degrees.append(len(node))
        subweights.append(weights[i])
        parent.append(par)
        for child in node:
            j = visit(child, i)
            subweights[i] += subweights[j]
        return i
    visit(tree, None)
    assert cursor == len(weights)
    return degrees, subweights, parent


def nearest(x: Q) -> int:
    # Either nearest integer is harmless at an exact half; marked points
    # are strictly closer than 1/(4N), so cannot be ties.
    return (2 * x.numerator + x.denominator) // (2 * x.denominator)


def packing_checks():
    cases = 0
    weighted_trees = 0
    count_checks = 0
    largest_size = 5
    largest_weight = 11
    for m in range(1, largest_size + 1):
        assert len(trees(m)) == math.comb(2 * (m - 1), m - 1) // m
        for total in range(m, largest_weight + 1):
            slot_count = 0
            for tree in trees(m):
                for weights in compositions(total, m):
                    degrees, sums, parent = tree_data(tree, weights)
                    weighted_trees += 1
                    slots = 1
                    for w, d in zip(weights, degrees):
                        slots *= math.comb(w + 1, d) if d <= w + 1 else 0
                    slot_count += slots
                    for q in range(1, total + 1):
                        marked = {i for i, s in enumerate(sums) if s % q == 0}
                        assert q * len(marked) <= total
                        # Independently compute the disjoint marked blocks.
                        block_weights = {i: 0 for i in marked}
                        for i, w in enumerate(weights):
                            j = i
                            while j is not None and j not in marked:
                                j = parent[j]
                            if j is not None:
                                block_weights[j] += w
                        assert all(b >= q and b % q == 0 for b in block_weights.values())
                        assert sum(block_weights.values()) <= total
                        cases += 1
            upper = 4 ** (m - 1) * total ** (m - 1) * (total + 1) ** (m - 1)
            assert slot_count <= upper
            count_checks += 1
    # A zero-weight unary vertex invalidates the packing assertion.
    _, sums, _ = tree_data(((),), (0, 3))
    assert sums == [3, 3] and 3 * 2 > sum((0, 3))
    return dict(weighted_trees=weighted_trees, divisor_packing_cases=cases,
                plane_tree_count_bounds=count_checks,
                zero_weight_counterexamples=1,
                maximum_vertices=largest_size, maximum_total_weight=largest_weight)


def clustering_checks():
    cases = 0
    nonempty = 0
    for denominator in range(2, 61):
        for numerator in range(1, denominator):
            if math.gcd(numerator, denominator) != 1:
                continue
            alpha = Q(numerator, denominator)
            for total in range(1, 31):
                marked = []
                for s in range(1, total + 1):
                    p = nearest(s * alpha)
                    error = abs(s * alpha - p)
                    if error < Q(1, 4 * total):
                        marked.append((s, p, error))
                if marked:
                    common = Q(marked[0][1], marked[0][0])
                    q, p = common.denominator, common.numerator
                    assert q <= total
                    dq = abs(q * alpha - p)
                    assert dq < Q(1, 4 * total)
                    for s, ps, error in marked:
                        assert Q(ps, s) == common and s % q == 0
                        assert error == (s // q) * dq
                    nonempty += 1
                cases += 1
    return dict(rational_alpha_and_weight_cases=cases, nonempty_marked_cases=nonempty,
                maximum_denominator=60, maximum_total_weight=30,
                interpretation="Exact finite rational tests of the clustering algebra; no irrational limsup tested.")


# Bivariate truncated polynomials with rational coefficients, keys (t-degree,z-degree).
Poly = dict[tuple[int, int], Q]


def add(a: Poly, b: Poly) -> Poly:
    out = defaultdict(Q, a)
    for key, value in b.items():
        out[key] += value
    return {k: v for k, v in out.items() if v}


def mul(a: Poly, b: Poly, order: int, degree: int) -> Poly:
    out = defaultdict(Q)
    for (i, n), x in a.items():
        for (j, k), y in b.items():
            if i + j <= order and n + k <= degree:
                out[i + j, n + k] += x * y
    return {k: v for k, v in out.items() if v}


def powers(a: Poly, top: int, order: int, degree: int):
    result = [{(0, 0): Q(1)}]
    for _ in range(top):
        result.append(mul(result[-1], a, order, degree))
    return result


def compose(outer: Poly, inner: Poly, order: int, degree: int) -> Poly:
    ps = powers(inner, degree, order, degree)
    result = defaultdict(Q)
    for (b, n), c in outer.items():
        for (a, k), v in ps[n].items():
            if a + b <= order:
                result[a + b, k] += c * v
    return {k: v for k, v in result.items() if v}


def linearizer(lam: Q, input_coeff: Poly, order: int, degree: int) -> Poly:
    h = {(0, 1): Q(1)}
    for a in range(1, order + 1):
        rhs = compose(input_coeff, h, order, degree)
        for n in range(2, degree + 1):
            value = rhs.get((a, n), Q(0)) / (lam ** n - lam)
            if value:
                h[a, n] = value
    return h


def inverse(h: Poly, order: int, degree: int) -> Poly:
    identity = {(0, 1): Q(1)}
    tail = {k: v for k, v in h.items() if k != (0, 1)}
    j = dict(identity)
    for a in range(1, order + 1):
        rhs = compose(tail, j, order, degree)
        for n in range(2, degree + 1):
            value = -rhs.get((a, n), Q(0))
            if value:
                j[a, n] = value
    return j


def tree_linearizer(lam: Q, input_coeff: Poly, order: int, degree: int) -> Poly:
    """Independent skeleton/slot version of the plane-tree formula."""
    result = defaultdict(Q, {(0, 1): Q(1)})
    labels = sorted({a for a, n in input_coeff})
    contributions = 0
    for m in range(1, order + 1):
        for label_word in itertools.product(labels, repeat=m):
            total_label = sum(label_word)
            if total_label > order:
                continue
            for total in range(m, degree):
                for tree in trees(m):
                    for weights in compositions(total, m):
                        degrees, sums, _ = tree_data(tree, weights)
                        term = lam ** (-m)
                        for a, w, d, s in zip(label_word, weights, degrees, sums):
                            if d > w + 1:
                                term = Q(0)
                                break
                            term *= input_coeff.get((a, w + 1), Q(0))
                            term *= math.comb(w + 1, d)
                            term /= lam ** s - 1
                        result[total_label, total + 1] += term
                        contributions += 1
    return {k: v for k, v in result.items() if v}, contributions


def operator_linearizer(lam: Q, coeff: Poly, order: int, degree: int) -> Poly:
    """Independent finite Neumann expansion for J(F)=lambda*J."""
    f = add({(0, 1): lam}, coeff)
    rotation = {(0, 1): lam}
    def linv(p):
        assert all(n >= 2 for (_, n) in p)
        return {(a, n): c / (lam ** n - lam) for (a, n), c in p.items()}
    term = linv(coeff)
    answer = {(0, 1): Q(1)}
    for depth in range(order):
        answer = add(answer, {key: (-1) ** (depth + 1) * c for key, c in term.items()})
        nop = add(compose(term, f, order, degree),
                  {key: -c for key, c in compose(term, rotation, order, degree).items()})
        term = linv(nop)
    assert not term
    return answer


def algebra_checks():
    order, degree = 4, 8
    tests = 0
    comparisons = 0
    contributions = 0
    records = []
    for lam in [Q(2), Q(2, 3), Q(-2)]:
        for kind in ["one_label_geometric", "two_colliding_labels"]:
            if kind == "one_label_geometric":
                coeff = {(1, n): Q(1, 3 ** (n - 1)) for n in range(2, degree + 1)}
            else:
                coeff = {(a, n): Q((-1) ** (a * n) * (a + n), (a + 1) ** n)
                         for a in (1, 2) for n in range(2, degree + 1)}
            h = linearizer(lam, coeff, order, degree)
            ht, number = tree_linearizer(lam, coeff, order, degree)
            contributions += number
            for a in range(order + 1):
                for n in range(degree + 1):
                    assert h.get((a, n), Q(0)) == ht.get((a, n), Q(0))
                    comparisons += 1
            f = add({(0, 1): lam}, coeff)
            rotation = {(0, 1): lam}
            ident = {(0, 1): Q(1)}
            j = inverse(h, order, degree)
            assert j == operator_linearizer(lam, coeff, order, degree)
            assert compose(f, h, order, degree) == compose(h, rotation, order, degree)
            assert compose(h, j, order, degree) == ident
            assert compose(j, h, order, degree) == ident
            assert compose(j, f, order, degree) == compose(rotation, j, order, degree)
            # No hidden sign convention: the first positive coefficient
            # of the inverse is the negative of the forward coefficient.
            for n in range(2, degree + 1):
                assert j.get((1, n), Q(0)) == -h.get((1, n), Q(0))
            tests += 6
            records.append(dict(multiplier=str(lam), input=kind, status="PASS"))
    return dict(cases=records, identity_groups=tests,
                coefficient_comparisons=comparisons,
                enumerated_tree_label_weight_terms=contributions,
                parameter_order=order, taylor_degree=degree,
                interpretation="Exact formal identities only; these rational multipliers do not test the unit-circle analytic estimate.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON (refuses an existing path).")
    args = parser.parse_args()
    if args.output is not None and args.output.exists():
        parser.error(f"Refusing to overwrite {args.output}; choose a fresh path.")
    report = dict(status="PASS", packing=packing_checks(), clustering=clustering_checks(),
                  formal_algebra=algebra_checks(),
                  limitations=["Not a proof-assistant verification.",
                  "No test proves infinite Hahn support summability or an analytic radius.",
                  "No finite computation establishes a small-divisor limsup or novelty."])
    text = json.dumps(report, indent=2)
    print(text)
    if args.output is not None:
        args.output.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
