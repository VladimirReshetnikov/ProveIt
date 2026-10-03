#!/usr/bin/env python3
"""Exact finite shadows of the surreal well-order paper.

Python 3.10+; standard library only. These tests do not verify infinite,
ordinal, class, or set-theoretic theorems. No floating point is used.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence


def sign_compare(s: tuple[int, ...], t: tuple[int, ...]) -> int:
    """Numerical sign comparison with minus < termination < plus."""
    for i in range(max(len(s), len(t))):
        a = s[i] if i < len(s) else 0
        b = t[i] if i < len(t) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def code(s: tuple[int, ...]) -> tuple[int, ...]:
    if any(x not in (-1, 1) for x in s):
        raise ValueError("Signs must be -1 or 1.")
    return tuple(bit for x in s for bit in ((0, 0) if x == -1 else (1, 1))) + (0, 1)


def ordinary_compare(a: Sequence[int], b: Sequence[int]) -> int:
    return (a > b) - (a < b)


def is_prefix(a: Sequence[int], b: Sequence[int]) -> bool:
    return len(a) <= len(b) and tuple(b[: len(a)]) == tuple(a)


def pair_encode(bits: Sequence[int]) -> tuple[int, ...]:
    return tuple(x for i, bit in enumerate(bits)
                 for x in ((2 * i, 2 * i + 1) if bit == 0 else (2 * i + 1, 2 * i)))


def common_prefix_formula(r: tuple[int, ...], s: tuple[int, ...]) -> frozenset[int]:
    """Literal finite version of the predecessor-relation definition."""
    if set(r) != set(s) or len(set(r)) != len(r) or len(set(s)) != len(s):
        raise ValueError("Inputs must be permutations of the same carrier.")
    rp, sp = {x: i for i, x in enumerate(r)}, {x: i for i, x in enumerate(s)}
    result = set()
    for x in r:
        ar = {y for y in r if rp[y] < rp[x]}
        bs = {y for y in s if sp[y] < sp[x]}
        if ar == bs and all((rp[u] < rp[v]) == (sp[u] < sp[v]) for u in ar for v in ar):
            result.add(x)
    return frozenset(result)


def common_prefix_direct(r: tuple[int, ...], s: tuple[int, ...]) -> tuple[int, ...]:
    out = []
    for a, b in zip(r, s):
        if a != b:
            break
        out.append(a)
    return tuple(out)


def adjacency_criterion(r: tuple[int, ...], s: tuple[int, ...]) -> bool:
    """The finite form: consecutive first labels and extreme remaining tails."""
    if not r < s:
        return False
    p = common_prefix_direct(r, s)
    k = len(p)
    residual = set(r) - set(p)
    a, b = r[k], s[k]
    return (not any(a < d < b for d in residual)
            and r[k + 1:] == tuple(sorted(residual - {a}, reverse=True))
            and s[k + 1:] == tuple(sorted(residual - {b})))


def schedule(rows: int, width: int) -> list[tuple[int, int]]:
    if rows < 1 or width < 1:
        raise ValueError("Positive dimensions are required.")
    return sorted(itertools.product(range(rows), range(width)),
                  key=lambda p: (max(p), p[0], p[1]))


def scheduler_encode(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    rows = []
    for i, x in enumerate(values):
        if not 0 <= x < width:
            raise ValueError("Row selector outside its row.")
        row = list(range(i * width, (i + 1) * width))
        row[0], row[x] = row[x], row[0]
        rows.append(row)
    return tuple(rows[i][j] for i, j in schedule(len(values), width))


def run_checks() -> dict[str, object]:
    counts: dict[str, int] = {}
    signs = [s for n in range(8) for s in itertools.product((-1, 1), repeat=n)]
    n = 0
    for s in signs:
        for t in signs:
            assert sign_compare(s, t) == ordinary_compare(code(s), code(t))
            if s != t:
                assert not is_prefix(code(s), code(t))
            n += 1
    counts["sign_code_order_and_prefix_pairs"] = n

    n = 0
    for size in range(9):
        words = list(itertools.product((0, 1), repeat=size))
        enc = {w: pair_encode(w) for w in words}
        for w, v in itertools.product(words, repeat=2):
            assert ordinary_compare(w, v) == ordinary_compare(enc[w], enc[v])
            n += 1
        for e in enc.values():
            assert sorted(e) == list(range(2 * size))
    counts["pair_orientation_order_pairs"] = n

    n = 0
    for size in range(1, 6):
        permutations = list(itertools.permutations(range(size)))
        for i, r in enumerate(permutations):
            for j, s in enumerate(permutations):
                c = common_prefix_formula(r, s)
                p = common_prefix_direct(r, s)
                assert c == frozenset(p)
                if r != s:
                    a = next(x for x in r if x not in c)
                    b = next(x for x in s if x not in c)
                    assert a != b
                    assert (a < b) == (r < s)
                assert adjacency_criterion(r, s) == (j == i + 1)
                n += 1
    counts["common_prefix_and_adjacency_pairs"] = n

    n = 0
    for size in (6, 7):
        permutations = list(itertools.permutations(range(size)))
        for r, s in zip(permutations, permutations[1:]):
            assert adjacency_criterion(r, s)
            n += 1
    counts["larger_adjacent_pairs"] = n

    n = 0
    for rows in range(1, 5):
        for width in range(1, 4):
            sc = schedule(rows, width)
            firsts = [sc.index((i, 0)) for i in range(rows)]
            assert firsts == sorted(firsts)
            words = list(itertools.product(range(width), repeat=rows))
            enc = {w: scheduler_encode(w, width) for w in words}
            for e in enc.values():
                assert sorted(e) == list(range(rows * width))
            for a, b in itertools.product(words, repeat=2):
                assert ordinary_compare(a, b) == ordinary_compare(enc[a], enc[b])
                n += 1
    counts["scheduler_product_order_pairs"] = n

    # A concrete illustration that relation-table lex differs from enumeration lex.
    perms = list(itertools.permutations(range(3)))
    def table(p: tuple[int, ...]) -> tuple[int, ...]:
        pos = {x: i for i, x in enumerate(p)}
        return tuple(int(pos[x] < pos[y]) for x in range(3) for y in range(3))
    different = next((r, s) for r in perms for s in perms
                     if (r < s) != (table(r) < table(s)) and r != s)
    return {
        "status": "PASS",
        "arithmetic": "exact finite combinatorics; standard-library Python",
        "scope_warning": "These finite tests prove no transfinite, class, or consistency theorem.",
        "counts": counts,
        "total_comparison_cases": sum(counts.values()),
        "relation_table_vs_enumeration_example": {
            "first_permutation": different[0],
            "second_permutation": different[1],
            "first_table": table(different[0]),
            "second_table": table(different[1]),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write a JSON record to this path.")
    args = parser.parse_args()
    results = run_checks()
    text = json.dumps(results, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
