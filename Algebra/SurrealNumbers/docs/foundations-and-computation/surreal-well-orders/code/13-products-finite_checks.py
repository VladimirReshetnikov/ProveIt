#!/usr/bin/env python3
"""Finite checks for the accompanying surreal well-order manuscript.

Uses only the Python standard library. These checks concern finite
representations and do NOT prove the transfinite/class-theoretic theorems.
Run from the archive root:
    python3 code/finite_checks.py --output data/finite_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


def compare(a: object, b: object) -> int:
    """Three-way comparison of orderable arguments."""
    return (a > b) - (a < b)  # type: ignore[operator]


def relation_data(order: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
    """Return relation bits and predecessor masks, independently of lex order."""
    n = len(order)
    positions = {x: i for i, x in enumerate(order)}
    relation = sum(1 << (x * n + y) for x in range(n) for y in range(n)
                   if positions[x] < positions[y])
    predecessors = tuple(sum(1 << y for y in range(n)
                             if positions[y] < positions[x]) for x in range(n))
    return relation, predecessors


def predecessor_compare(
    r: tuple[int, ...], s: tuple[int, ...],
    rd: tuple[int, tuple[int, ...]], sd: tuple[int, tuple[int, ...]],
    internal_masks: Sequence[int],
) -> int:
    """Largest common labeled prefix, defined using predecessor relations."""
    rr, rp = rd
    sr, sp = sd
    difference = rr ^ sr
    common = 0
    for x in range(len(r)):
        if rp[x] == sp[x] and not (difference & internal_masks[rp[x]]):
            common |= 1 << x
    if common == (1 << len(r)) - 1:
        return 0
    a = next(x for x in r if not common & (1 << x))
    b = next(x for x in s if not common & (1 << x))
    assert a != b
    return compare(a, b)


def finite_orders(max_n: int) -> dict[str, int]:
    stats: dict[str, int] = defaultdict(int)
    for n in range(1, max_n + 1):
        orders = list(itertools.permutations(range(n)))
        data = [relation_data(r) for r in orders]
        masks = [sum(1 << (x * n + y) for x in range(n) for y in range(n)
                     if mask & (1 << x) and mask & (1 << y))
                 for mask in range(1 << n)]
        for i, r in enumerate(orders):
            for j, s in enumerate(orders):
                assert predecessor_compare(r, s, data[i], data[j], masks) == compare(r, s)
                stats['relation_vs_lex_pairs'] += 1

        if n <= 4:
            for i, j, k in itertools.combinations(range(len(orders)), 3):
                assert predecessor_compare(orders[i], orders[k], data[i], data[k], masks) < 0
                stats['strict_transitivity_triples'] += 1

        cylinders: dict[tuple[int, ...], list[int]] = defaultdict(list)
        levels: dict[int, list[tuple[int, ...]]] = defaultdict(list)
        for i, r in enumerate(orders):
            for length in range(n + 1):
                cylinders[r[:length]].append(i)
        for p, rows in cylinders.items():
            assert rows == list(range(rows[0], rows[-1] + 1))
            levels[len(p)].append(p)
            stats['convex_cylinders'] += 1
            completed = p + tuple(x for x in range(n) if x not in p)
            assert completed[:len(p)] == p
            assert sorted(completed) == list(range(n))
            moved = {i: completed[i] for i in range(n) if completed[i] != i}
            assert set(moved) == set(moved.values())
            evaluated = tuple(moved.get(i, i) for i in range(n))
            assert evaluated == completed
            stats['canonical_prefix_completions'] += 1

        for cut in range(1, len(orders)):
            previous: tuple[int, ...] = ()
            failure: int | None = None
            for length in range(n + 1):
                crossing = [p for p in levels[length]
                            if cylinders[p][0] < cut <= cylinders[p][-1]]
                assert len(crossing) <= 1
                if crossing:
                    assert failure is None
                    assert crossing[0][:len(previous)] == previous
                    previous = crossing[0]
                    assert orders[cut - 1][:length] == orders[cut][:length] == previous
                else:
                    if failure is None:
                        failure = length
                stats['cut_level_uniqueness_checks'] += 1
            assert failure is not None and failure > 0
            assert len(previous) == failure - 1
            children = [p for p in levels[failure] if p[:-1] == previous]
            lower = [p[-1] for p in children if cylinders[p][-1] < cut]
            upper = [p[-1] for p in children if cylinders[p][0] >= cut]
            assert lower and upper and max(lower) < min(upper)
            assert len(lower) + len(upper) == len(children)
            stats['successor_failure_partitions'] += 1
    return dict(stats)


def finite_sign_value(signs: str) -> Fraction:
    """Independent dyadic evaluation of a finite surreal sign sequence."""
    if not signs:
        return Fraction(0)
    if any(c not in '+-' for c in signs):
        raise ValueError('A sign sequence must contain only + and -.')
    initial = signs[0]
    run = next((i for i, c in enumerate(signs) if c != initial), len(signs))
    value = Fraction(run if initial == '+' else -run)
    for i in range(run, len(signs)):
        value += Fraction(1 if signs[i] == '+' else -1, 2 ** (i - run + 1))
    return value


def central_compare(p: Sequence[Fraction], q: Sequence[Fraction]) -> int:
    if any(x == 0 for x in itertools.chain(p, q)):
        raise ValueError('Zero is reserved for termination, not an ordinary letter.')
    for i in range(max(len(p), len(q))):
        a = p[i] if i < len(p) else Fraction(0)
        b = q[i] if i < len(q) else Fraction(0)
        if a != b:
            return compare(a, b)
    return 0


def central_words() -> dict[str, int]:
    letters = {
        Fraction(-2): '--', Fraction(-1): '-', Fraction(-1, 2): '-+',
        Fraction(1, 2): '+-', Fraction(1): '+', Fraction(2): '++',
    }
    for x, s in letters.items():
        assert finite_sign_value(s) == x
    blocks = {x: ''.join(c * 2 for c in s) + '+-' for x, s in letters.items()}
    for x, y in itertools.permutations(letters, 2):
        assert not blocks[x].startswith(blocks[y])
        assert compare(finite_sign_value(blocks[x]), finite_sign_value(blocks[y])) == compare(x, y)

    words = [w for n in range(4) for w in itertools.product(letters, repeat=n)]
    codes = {w: ''.join(blocks[x] for x in w) for w in words}
    values = {w: finite_sign_value(codes[w]) for w in words}
    assert len(set(values.values())) == len(words)
    all_pairs = injective_pairs = 0
    for p in words:
        assert len(codes[p]) == sum(2 * len(letters[x]) + 2 for x in p)
        for q in words:
            assert central_compare(p, q) == compare(values[p], values[q])
            all_pairs += 1
            if len(set(p)) == len(p) and len(set(q)) == len(q):
                injective_pairs += 1
    # Zero-padding would collapse these distinct invalid words.
    invalid_p = (Fraction(1),)
    invalid_q = (Fraction(1), Fraction(0))
    assert tuple(invalid_p[i] if i < len(invalid_p) else Fraction(0) for i in range(3)) == \
           tuple(invalid_q[i] if i < len(invalid_q) else Fraction(0) for i in range(3))
    try:
        central_compare(invalid_p, invalid_q)
    except ValueError:
        pass
    else:
        raise AssertionError('The reserved marker was incorrectly admitted as a letter.')
    return {
        'letters': len(letters), 'max_word_length': 3,
        'words': len(words), 'all_word_pairs': all_pairs,
        'injective_word_pairs_included': injective_pairs,
        'distinct_rational_code_values': len(set(values.values())),
        'reserved_marker_collision_and_rejection': 1,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6, choices=range(1, 7))
    parser.add_argument('--output', type=Path, default=Path('data/finite_results.json'))
    args = parser.parse_args()
    report = {
        'status': 'all finite checks passed',
        'scope': 'Finite representations only; no transfinite or class-theory verification.',
        'python_version': platform.python_version(),
        'max_permutation_alphabet_size': args.max_n,
        'finite_order_checks': finite_orders(args.max_n),
        'central_word_checks': central_words(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
