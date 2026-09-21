#!/usr/bin/env python3
"""Exact, dependency-free checks for the proof of OEIS A199085.

Run: python3 verify.py --out-dir artifacts
All arithmetic is integer or fractions.Fraction. No floating-point
numerical differentiation, symbolic-math package, or network is used.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Any

State = tuple[int, int]  # (F''(1)/2, F'''(1)/3)
Tree = Any  # None is a leaf; an ordered pair is exponentiation.
ORDER = 3


def closed_count(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    return 1 if n < 3 else (n * n - 2) // 3


def predicted_states(n: int) -> set[State]:
    if n < 1:
        raise ValueError("n must be positive")
    return {(n - 1, (n - 1) ** 2)} | {
        (k, k * k + 2 * s)
        for k in range(1, n - 1)
        for s in range(1, n - k)
    }


def overlap_count(n: int) -> int:
    return sum(n - 3 * j for j in range(2, (n - 1) // 3 + 1))


def state_dp(limit: int) -> list[set[State]]:
    """Enumerate exact derivative states from the local composition law.

    The right child's third derivative is irrelevant, so its actual
    depth projection is used. No closed formula for that projection,
    for the state set, or for its cardinality is assumed here.
    """
    states: list[set[State]] = [set(), {(0, 0)}]
    depths: list[set[int]] = [set(), {0}]
    for n in range(2, limit + 1):
        current = set()
        for j in range(1, n):
            for k, b in states[j]:
                for ell in depths[n - j]:
                    current.add((k + 1, b + 2 * k + 2 * ell + 1))
        states.append(current)
        depths.append({k for k, _ in current})
    return states


def poly_add(a, b):
    return tuple(a[i] + b[i] for i in range(ORDER + 1))


def poly_scale(a, c):
    return tuple(c * value for value in a)


def poly_mul(a, b):
    return tuple(sum(a[j] * b[i - j] for j in range(i + 1))
                 for i in range(ORDER + 1))


def poly_log(a):
    """log(1+w) modulo t^4, independently of the derivative recurrence."""
    if a[0] != 1:
        raise ValueError("log input must have constant term 1")
    w = (Fraction(0),) + tuple(a[1:])
    answer = (Fraction(0),) * (ORDER + 1)
    power = (Fraction(1),) + (Fraction(0),) * ORDER
    for j in range(1, ORDER + 1):
        power = poly_mul(power, w)
        answer = poly_add(answer, poly_scale(power, Fraction((-1)**(j+1), j)))
    return answer


def poly_exp(a):
    """exp(w) modulo t^4 for w(0)=0."""
    if a[0] != 0:
        raise ValueError("exp input must have constant term 0")
    power = (Fraction(1),) + (Fraction(0),) * ORDER
    answer = power
    for j in range(1, ORDER + 1):
        power = poly_mul(power, a)
        answer = poly_add(answer, poly_scale(power, Fraction(1, math.factorial(j))))
    return answer


@lru_cache(maxsize=None)
def jet(tree: Tree) -> tuple[Fraction, ...]:
    if tree is None:
        return (Fraction(1), Fraction(1), Fraction(0), Fraction(0))
    left, right = tree
    return poly_exp(poly_mul(jet(right), poly_log(jet(left))))


def jet_state(tree: Tree) -> State:
    coefficients = jet(tree)
    assert coefficients[:2] == (1, 1)
    k, b = coefficients[2], 2 * coefficients[3]
    assert k.denominator == 1 and b.denominator == 1
    return int(k), int(b)


@lru_cache(maxsize=None)
def all_trees(n: int) -> tuple[Tree, ...]:
    if n == 1:
        return (None,)
    return tuple((left, right) for j in range(1, n)
                 for left in all_trees(j) for right in all_trees(n - j))


def right_comb(n: int) -> Tree:
    if n < 1:
        raise ValueError("A comb needs at least one leaf")
    tree = None
    for _ in range(n - 1):
        tree = (None, tree)
    return tree


def left_comb(n: int) -> Tree:
    if n < 1:
        raise ValueError("A comb needs at least one leaf")
    tree = None
    for _ in range(n - 1):
        tree = (tree, None)
    return tree


def prescribed_depth(m: int, depth: int) -> Tree:
    if not (m >= 2 and 1 <= depth <= m - 1):
        raise ValueError("Require m>=2 and 1<=depth<=m-1")
    tree = (None, right_comb(m - depth))
    for _ in range(depth - 1):
        tree = (tree, None)
    return tree


def witness(n: int, k: int, b: int) -> Tree:
    if n >= 1 and (k, b) == (n - 1, (n - 1)**2):
        return left_comb(n)
    if not (1 <= k <= n - 2) or (b - k*k) % 2:
        raise ValueError("Not an admissible state")
    s = (b - k*k) // 2
    if not 1 <= s <= n - k - 1:
        raise ValueError("Not an admissible state")
    tree = (None, prescribed_depth(n - k, s))
    for _ in range(k - 1):
        tree = (tree, None)
    return tree


def leaf_count(tree: Tree) -> int:
    return 1 if tree is None else leaf_count(tree[0]) + leaf_count(tree[1])


def expression(tree: Tree) -> str:
    return "x" if tree is None else f"({expression(tree[0])}^{expression(tree[1])})"


def gf_coefficients(limit: int) -> list[int]:
    """Expand the exact rational function printed in OEIS A199085."""
    numerator = [0, -1, 1, -1, 0, -2, 0, 1]
    denominator = [-1, 2, -1, 1, -2, 1]
    coefficients = []
    for n in range(limit + 1):
        rhs = numerator[n] if n < len(numerator) else 0
        rhs -= sum(denominator[j] * coefficients[n-j]
                   for j in range(1, min(n, len(denominator)-1) + 1))
        assert rhs % denominator[0] == 0
        coefficients.append(rhs // denominator[0])
    return coefficients


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dp-limit", type=int, default=60)
    parser.add_argument("--tree-limit", type=int, default=10)
    parser.add_argument("--witness-limit", type=int, default=20)
    parser.add_argument("--series-limit", type=int, default=1000)
    parser.add_argument("--out-dir", type=Path, default=Path("artifacts"))
    args = parser.parse_args()
    if not __debug__:
        parser.error("Run without -O: verification requires assertions")
    if min(args.dp_limit, args.tree_limit, args.witness_limit, args.series_limit) < 1:
        parser.error("All limits must be positive")
    if args.tree_limit > 12:
        parser.error("Exhaustive tree enumeration is intentionally limited to n<=12")
    if args.series_limit < max(args.dp_limit, args.tree_limit, args.witness_limit):
        parser.error("series-limit must be at least the other limits")
    args.out_dir.mkdir(parents=True, exist_ok=True)
    dp = state_dp(args.dp_limit)
    rows = []
    for n in range(1, args.dp_limit + 1):
        expected = predicted_states(n)
        assert dp[n] == expected, ("state classification", n)
        count = len({b for _, b in dp[n]})
        pair_count = 1 + (n - 1)*(n - 2)//2
        assert len(dp[n]) == pair_count, ("joint state count", n)
        assert count == pair_count - overlap_count(n) == closed_count(n), n
        rows.append({"n": n, "joint_states": pair_count,
                     "overlap_correction": overlap_count(n), "a_n": count})

    tree_checks = []
    for n in range(1, args.tree_limit + 1):
        trees = all_trees(n)
        catalan = math.comb(2*(n-1), n-1)//n
        assert len(trees) == catalan, ("tree enumeration", n)
        actual = {jet_state(t) for t in trees}
        assert actual == predicted_states(n), ("independent Taylor jets", n)
        tree_checks.append({"n": n, "trees": len(trees),
                            "joint_states": len(actual),
                            "distinct_third_derivatives": len({b for _, b in actual})})

    witness_checks = 0
    for n in range(1, args.witness_limit + 1):
        for k, b in predicted_states(n):
            tree = witness(n, k, b)
            assert leaf_count(tree) == n
            assert jet_state(tree) == (k, b), ("constructed witness", n, k, b)
            witness_checks += 1

    coefficients = gf_coefficients(args.series_limit)
    assert coefficients[0] == 0
    for n in range(1, args.series_limit + 1):
        assert coefficients[n] == closed_count(n), ("rational g.f.", n)
        assert coefficients[n] == (1 + (n-1)*(n-2)//2 - overlap_count(n)), n
    for n in range(3, args.series_limit - 2):
        assert coefficients[n+3] - coefficients[n] == 2*n + 3
    for n in range(8, args.series_limit + 1):
        assert coefficients[n] == (2*coefficients[n-1] - coefficients[n-2]
                                   + coefficients[n-3] - 2*coefficients[n-4]
                                   + coefficients[n-5])

    with (args.out_dir / "state_counts.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    with (args.out_dir / "coefficients.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "a_n"])
        writer.writerows(enumerate(coefficients[1:], 1))
    states_json = {str(n): [{"second_derivative": 2*k, "third_derivative": 3*b}
                           for k, b in sorted(dp[n])]
                   for n in range(1, args.dp_limit + 1)}
    (args.out_dir / "derivative_states.json").write_text(
        json.dumps(states_json, indent=2) + "\n", encoding="utf-8")
    examples = {str(n): [{"second_derivative": 2*k, "third_derivative": 3*b,
                         "parenthesization": expression(witness(n, k, b))}
                        for k, b in sorted(predicted_states(n))]
                for n in (5, 7)}
    (args.out_dir / "witnesses_n5_n7.json").write_text(
        json.dumps(examples, indent=2) + "\n", encoding="utf-8")
    report = {"status": "PASS", "arithmetic": "exact integer and rational",
              "python_version": sys.version.split()[0],
              "dp_checked_through_n": args.dp_limit,
              "exhaustive_taylor_checks": tree_checks,
              "constructed_witnesses_checked": witness_checks,
              "witnesses_checked_through_n": args.witness_limit,
              "gf_coefficients_checked_through_n": args.series_limit,
              "claim": "Finite computations support; the article supplies the all-n proof."}
    text = json.dumps(report, indent=2) + "\n"
    (args.out_dir / "verification_report.json").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
