#!/usr/bin/env python3
"""Finite regression checks for the manuscript's coding and adjacency rules.
These are tests of finite instances, not proofs of transfinite statements.
Python 3.10+, standard library only.
"""
from __future__ import annotations
from itertools import permutations, product
from functools import cmp_to_key
import json
from pathlib import Path


def compare(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return (a > b) - (a < b)


def surreal_compare(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        if x != y:
            return (x > y) - (x < y)
    return 0


def code(a: tuple[int, ...]) -> tuple[int, ...]:
    out: list[int] = []
    for sign in a:
        if sign not in (-1, 1):
            raise ValueError('A sign must be -1 or 1')
        out.extend((0, 0) if sign == -1 else (1, 1))
    out.extend((0, 1))
    return tuple(out)


def adjacent_rule(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    if not a < b or len(a) != len(b) or set(a) != set(b):
        return False
    d = next(i for i in range(len(a)) if a[i] != b[i])
    residual = sorted(set(a[d:]))
    i = residual.index(a[d])
    return (i + 1 < len(residual) and residual[i + 1] == b[d]
            and a[d + 1:] == tuple(sorted(set(residual) - {a[d]}, reverse=True))
            and b[d + 1:] == tuple(sorted(set(residual) - {b[d]})))


def paired(bits: tuple[int, ...]) -> tuple[int, ...]:
    out: list[int] = []
    for i, bit in enumerate(bits):
        pair = (2 * i, 2 * i + 1)
        out.extend(pair if bit == 0 else pair[::-1])
    return tuple(out)


def run() -> dict:
    adjacency_pairs = 0
    adjacency_all_pair_checks = 0
    for n in range(1, 8):
        ps = list(permutations(range(n)))
        for a, b in zip(ps, ps[1:]):
            assert adjacent_rule(a, b), (a, b)
            adjacency_pairs += 1
        # Exhaustive positive and negative checks on manageable instances.
        if n <= 5:
            for i, a in enumerate(ps):
                for j in range(i + 1, len(ps)):
                    assert adjacent_rule(a, ps[j]) == (j == i + 1)
                    adjacency_all_pair_checks += 1
    paired_comparisons = 0
    for m in range(8):
        bs = list(product((0, 1), repeat=m))
        images = [paired(s) for s in bs]
        assert all(set(p) == set(range(2 * m)) for p in images)
        for i, s in enumerate(bs):
            for j, t in enumerate(bs):
                assert compare(s, t) == compare(images[i], images[j])
                paired_comparisons += 1
    words = [s for n in range(7) for s in product((-1, 1), repeat=n)]
    code_comparisons = 0
    for s in words:
        for t in words:
            cs, ct = code(s), code(t)
            assert surreal_compare(s, t) == compare(cs, ct)
            if s != t:
                assert cs != ct[:len(cs)]
                assert ct != cs[:len(ct)]
            code_comparisons += 1
    result = {
        'status': 'PASS',
        'adjacent_pairs_checked_n_at_most_7': adjacency_pairs,
        'all_ordered_distinct_pairs_checked_n_at_most_5': adjacency_all_pair_checks,
        'paired_coding_comparisons_m_at_most_7': paired_comparisons,
        'sign_words_length_at_most_6': len(words),
        'sign_coding_comparisons': code_comparisons,
        'scope': 'Finite regression tests only; no transfinite or Lean verification.'
    }
    return result


if __name__ == '__main__':
    result = run()
    output = Path(__file__).with_name('verification_results.json')
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
