#!/usr/bin/env python3
"""Exact checks for multi-label open-query games (standard library only).

Minimax over all open questions and breadth-first ideal search are independent
optimization routines. Run without -O; assertions are verification conditions.
"""
from __future__ import annotations
import argparse
from collections import deque
from functools import lru_cache
from itertools import product
from pathlib import Path
import csv
import json
import platform
import time
from typing import Iterable, Sequence


def clog(m: int) -> int:
    if m < 1:
        raise ValueError('positive argument required')
    return (m - 1).bit_length()


def bits(mask: int) -> Iterable[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def posets(n: int) -> Iterable[tuple[int, ...]]:
    """Transitive strict-predecessor masks; labels are a linear extension."""
    if n == 0:
        yield ()
    else:
        for pred in posets(n - 1):
            for down in range(1 << (n - 1)):
                if all(pred[x] & ~down == 0 for x in bits(down)):
                    yield pred + (down,)


def upper_sets(pred: Sequence[int]) -> list[int]:
    full = (1 << len(pred)) - 1
    return [full ^ down for down in range(full + 1)
            if all(pred[x] & ~down == 0 for x in bits(down))]


def minimax(pred: Sequence[int], color: Sequence[int],
            opens: Sequence[int]) -> tuple[int, int]:
    """Optimal depth and leaf count via exhaustive legal-question minimax."""
    @lru_cache(None)
    def visit(mask: int) -> tuple[int, int]:
        if len({color[x] for x in bits(mask)}) <= 1:
            return 0, int(bool(mask))
        depth, leaves = len(color), len(color)
        seen = set()
        for op in opens:
            yes = op & mask
            no = mask ^ yes
            if not yes or not no or yes in seen:
                continue
            seen.add(yes)
            dy, ly = visit(yes)
            dn, ln = visit(no)
            depth = min(depth, 1 + max(dy, dn))
            leaves = min(leaves, ly + ln)
        return depth, leaves
    return visit((1 << len(color)) - 1)


def transition(pred: Sequence[int], color: Sequence[int], ideal: int, a: int) -> int:
    out = ideal
    for x in range(len(color)):
        if color[x] == a and pred[x] & ~out == 0:
            out |= 1 << x
    return out


def layer_word(pred: Sequence[int], color: Sequence[int], q: int) -> tuple[int, ...]:
    """Shortest word via breadth-first search on reachable ideals."""
    full = (1 << len(color)) - 1
    queue = deque([0])
    back: dict[int, tuple[int, int] | None] = {0: None}
    while queue:
        ideal = queue.popleft()
        if ideal == full:
            word = []
            while back[ideal] is not None:
                previous, a = back[ideal]  # type: ignore[misc]
                word.append(a)
                ideal = previous
            return tuple(reversed(word))
        for a in range(q):
            nxt = transition(pred, color, ideal, a)
            if nxt not in back:
                back[nxt] = ideal, a
                queue.append(nxt)
    raise AssertionError('Every finite colored poset is layerable')


def greedy_map(pred: Sequence[int], color: Sequence[int], word: Sequence[int]):
    positions = []
    for x, a in enumerate(color):
        lower = max((positions[y] for y in bits(pred[x])), default=0)
        pos = next((j for j in range(lower, len(word)) if word[j] == a), None)
        if pos is None:
            return None
        positions.append(pos)
    return tuple(positions)


def closure_test(pred: Sequence[int], color: Sequence[int], word: Sequence[int]) -> bool:
    """Closed-set elimination: closure in the upper topology is down-closure."""
    remaining = (1 << len(color)) - 1
    for a in reversed(word):
        keep = sum(1 << x for x in bits(remaining) if color[x] != a)
        remaining = keep
        for x in bits(keep):
            remaining |= pred[x]
    return remaining == 0


def chain_words(pred: Sequence[int], color: Sequence[int]) -> set[tuple[int, ...]]:
    words = set()
    for mask in range(1, 1 << len(color)):
        chain = tuple(bits(mask))
        if all((pred[b] >> a) & 1 for a, b in zip(chain, chain[1:])):
            reduced = []
            for x in chain:
                if not reduced or reduced[-1] != color[x]:
                    reduced.append(color[x])
            words.add(tuple(reduced))
    return words


def subsequence(small: Sequence[int], big: Sequence[int]) -> bool:
    p = 0
    for a in big:
        if p < len(small) and small[p] == a:
            p += 1
    return p == len(small)


def brute_scs(words: Iterable[Sequence[int]], q: int, bound: int) -> tuple[int, ...]:
    targets = list(words)
    for length in range(bound + 1):
        for word in product(range(q), repeat=length):
            if all(subsequence(s, word) for s in targets):
                return word
    raise ValueError('No common supersequence within bound')


def cyclic(pred: Sequence[int], color: Sequence[int], q: int):
    """(Prefix length, 1-based ranks, starting color), over q rotations."""
    if q < 1 or any(a < 0 or a >= q for a in color):
        raise ValueError('Invalid alphabet')
    best = None
    for start in range(q):
        ranks = []
        for x, a in enumerate(color):
            lower = max((ranks[y] for y in bits(pred[x])), default=1)
            ranks.append(lower + (a - start - (lower - 1)) % q)
        candidate = max(ranks, default=0), tuple(ranks), start
        if best is None or candidate[0] < best[0]:
            best = candidate
    return best


def binary_formula(pred: Sequence[int], color: Sequence[int]) -> int:
    ending = [[0, 0] for _ in color]
    longest = [0, 0]
    for x, a in enumerate(color):
        ending[x][a] = 1
        for y in bits(pred[x]):
            for start in range(2):
                if ending[y][start]:
                    ending[x][start] = max(ending[x][start],
                        ending[y][start] + int(color[y] != a))
        for start in range(2):
            longest[start] = max(longest[start], ending[x][start])
    a, b = longest
    return min(max(a, b + 1), max(b, a + 1))


def disjoint_chains(words: Sequence[Sequence[int]]):
    pred, color = [], []
    for word in words:
        earlier = 0
        for a in word:
            pred.append(earlier)
            earlier |= 1 << len(color)
            color.append(a)
    return tuple(pred), tuple(color)


def tree(ranks: Sequence[int], word: Sequence[int], lo=1, hi=None) -> dict:
    if hi is None:
        hi = len(word)
    if lo == hi:
        return {'color': word[lo - 1], 'layer': lo}
    cut = (lo + hi) // 2 + 1
    op = sum(1 << x for x, r in enumerate(ranks) if r >= cut)
    return {'open_mask': op, 'cut': cut,
            'no': tree(ranks, word, lo, cut - 1),
            'yes': tree(ranks, word, cut, hi)}


def check_tree(node: dict, pred: Sequence[int], color: Sequence[int]) -> int:
    def walk(t, x):
        if 'color' in t:
            assert t['color'] == color[x]
            return 0
        op = t['open_mask']
        assert all(not ((op >> y) & 1) or ((op >> z) & 1)
                   for z in range(len(color)) for y in bits(pred[z]))
        return 1 + walk(t['yes'] if (op >> x) & 1 else t['no'], x)
    return max(walk(node, x) for x in range(len(color)))


def examples() -> dict:
    families = []
    restricted = []
    for q in range(2, 5):
        for h in range(1, 5):
            for s in range(1, q + 1):
                words = [w for w in product(range(q), repeat=h)
                         if w[0] < s and all(a != b for a, b in zip(w, w[1:]))]
                expected = s + (q - 1) * (h - 1)
                master = tuple(i % q for i in range(expected))
                assert all(subsequence(w, master) for w in words)
                independently_optimized = q <= 3 and h <= 3
                if independently_optimized:
                    assert len(brute_scs(words, q, expected)) == expected
                restricted.append({'q': q, 'word_length': h, 'starting_colors': s,
                                   'optimal_layers': expected,
                                   'brute_force_optimum_checked': independently_optimized})
    for q in range(2, 5):
        for h in range(1, 5):
            words = [w for w in product(range(q), repeat=h)
                     if all(a != b for a, b in zip(w, w[1:]))]
            m = (q - 1) * h + 1
            master = tuple(i % q for i in range(m))
            assert all(subsequence(w, master) for w in words)
            if q <= 3 and h <= 3:
                assert len(brute_scs(words, q, m)) == m
            families.append({'q': q, 'h': h, 'chains': len(words),
                             'points': h * len(words), 'optimal_layers': m,
                             'component_depth': clog(h), 'sum_depth': clog(m)})
    words = [(a, b) for a in range(3) for b in range(3) if a != b]
    pred, color = disjoint_chains(words)
    master = (0, 1, 2, 0, 1)
    ranks = tuple(j + 1 for j in greedy_map(pred, color, master))
    strategy = tree(ranks, master)
    assert check_tree(strategy, pred, color) == 3
    assert len(layer_word(pred, color, 3)) == 5
    pp, cc = disjoint_chains([(2, 1, 0, 2)])
    prefix_example = cyclic(pp, cc, 3)
    assert prefix_example[0] == 7 and len(layer_word(pp, cc, 3)) == 4
    count = 0
    small_words = [w for k in range(1, 4) for w in product(range(3), repeat=k)
                   if w[0] != 2 and all(a != b for a, b in zip(w, w[1:]))]
    for left in small_words:
        for right in small_words:
            original = len(brute_scs([left, right], 3, len(left) + len(right)))
            for k in range(1, 7):
                budget = 1 << clog(k)
                t = budget - k
                prefix = tuple(2 if (t - 1 - j) % 2 == 0 else 0 for j in range(t))
                pp, cc = disjoint_chains([prefix + left, prefix + right])
                padded = len(layer_word(pp, cc, 3))
                assert padded == t + original
                assert (clog(padded) <= clog(k)) == (original <= k)
                count += 1
    return {'sharp_families': families, 'restricted_start_families': restricted,
            'padding_checks': count,
            'twelve_point_certificate': {'chains': words,
                'strict_predecessor_masks': pred, 'colors': color, 'word': master,
                'ranks_1_based': ranks, 'tree': strategy},
            'cyclic_prefix_example': {'chain': [2, 1, 0, 2],
                'prefix_length': prefix_example[0], 'ranks': prefix_example[1],
                'start': prefix_example[2], 'optimal_layers': 4}}


def main():
    if not __debug__:
        raise SystemExit('Run without -O; assertions are required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=5, choices=range(1, 7))
    parser.add_argument('--brute-n', type=int, default=4, choices=range(0, 5))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'results')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    rows = []
    candidate_checks = 0
    for n in range(1, args.max_n + 1):
        counts, brute_counts, np = {2: 0, 3: 0}, {2: 0, 3: 0}, 0
        for pred in posets(n):
            np += 1
            opens = upper_sets(pred)
            for q in (2, 3):
                for color in product(range(q), repeat=n):
                    depth, leaves = minimax(pred, color, opens)
                    word = layer_word(pred, color, q)
                    assert len(word) == leaves, (pred, color, leaves, word)
                    assert depth == clog(leaves), (pred, color, depth, leaves)
                    assert greedy_map(pred, color, word) is not None
                    approximate, ranks, rotation = cyclic(pred, color, q)
                    assert approximate <= 1 + (q - 1) * (leaves - 1)
                    assert clog(approximate) <= depth + clog(q - 1)
                    assert all(ranks[y] <= ranks[x]
                               for x in range(n) for y in bits(pred[x]))
                    if q == 2:
                        assert binary_formula(pred, color) == leaves
                    if n <= args.brute_n:
                        chains = chain_words(pred, color)
                        assert len(brute_scs(chains, q, n)) == leaves
                        for length in range(1, n + 1):
                            for candidate in product(range(q), repeat=length):
                                embeds = all(subsequence(w, candidate) for w in chains)
                                assert (greedy_map(pred, color, candidate) is not None) == embeds
                                assert closure_test(pred, color, candidate) == embeds
                                candidate_checks += 1
                        brute_counts[q] += 1
                    counts[q] += 1
        row = {'n': n, 'naturally_labelled_posets': np,
               'binary_colorings': counts[2], 'ternary_colorings': counts[3],
               'binary_chain_cross_checks': brute_counts[2],
               'ternary_chain_cross_checks': brute_counts[3]}
        rows.append(row)
        print(json.dumps(row), flush=True)
    extra = examples()
    result = {'description': 'Exact finite tests, not a formal proof or priority audit',
              'python': platform.python_version(), 'max_n': args.max_n,
              'brute_n': args.brute_n, 'rows': rows,
              'total_colorings': sum(r['binary_colorings'] + r['ternary_colorings'] for r in rows),
              'total_posets': sum(r['naturally_labelled_posets'] for r in rows),
              'candidate_word_checks': candidate_checks,
              'total_chain_cross_checks': sum(r['binary_chain_cross_checks'] + r['ternary_chain_cross_checks'] for r in rows),
              'elapsed_seconds': round(time.perf_counter() - start, 3),
              **extra, 'all_checks_passed': True}
    (args.output / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    (args.output / 'strategy_certificate.json').write_text(
        json.dumps(extra['twelve_point_certificate'], indent=2) + '\n')
    for name, data in [('poset_counts', rows), ('sharp_families', extra['sharp_families']),
                       ('restricted_start_families', extra['restricted_start_families'])]:
        with (args.output / (name + '.csv')).open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=list(data[0]))
            writer.writeheader()
            writer.writerows(data)
    print(f"PASS: {result['total_colorings']:,} colored-poset checks; "
          f"{result['total_chain_cross_checks']:,} chain-language checks; "
          f"{extra['padding_checks']:,} padding checks.", flush=True)
    print(f"Elapsed: {result['elapsed_seconds']} seconds", flush=True)


if __name__ == '__main__':
    main()
