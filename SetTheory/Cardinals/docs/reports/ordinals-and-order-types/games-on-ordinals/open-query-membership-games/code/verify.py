#!/usr/bin/env python3
"""Exact, standard-library verification of finite open-query game formulae.

The transfinite/Hausdorff results in the article are proved analytically.  Finite
posets carry their Alexandrov upper-set topology, not a Hausdorff approximation
to ordinal intervals.  This script independently compares:
  (1) exhaustive minimax over all open queries;
  (2) canonical alternating-closure chains;
  (3) the alternating-chain dynamic program.

Default: all naturally labelled posets of size at most five and every target.
Every finite poset admits a natural labelling, but these are NOT isomorphism
classes.  No third-party dependencies and no floating-point arithmetic.
"""
from __future__ import annotations
import argparse
import csv
import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from time import perf_counter
from typing import Iterator


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError('ceil_log2 requires a positive integer')
    return (n - 1).bit_length()


def natural_posets(n: int) -> Iterator[tuple[int, ...]]:
    """Yield transitive strict upper rows, with all comparisons i < j."""
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        rows = [0] * n
        for k, (i, j) in enumerate(pairs):
            if mask >> k & 1:
                rows[i] |= 1 << j
        valid = True
        for i in range(n):
            js = rows[i]
            while js:
                b = js & -js
                j = b.bit_length() - 1
                if rows[j] & ~rows[i]:
                    valid = False
                    break
                js -= b
            if not valid:
                break
        if valid:
            yield tuple(rows)


def upsets(rows: tuple[int, ...]) -> tuple[int, ...]:
    n = len(rows)
    return tuple(s for s in range(1 << n)
                 if all(not (s >> i & 1) or not (rows[i] & ~s)
                        for i in range(n)))


def closure_table(rows: tuple[int, ...]) -> list[int]:
    """Closure is downward closure in the upper-set topology."""
    n = len(rows)
    downs = [1 << j for j in range(n)]
    for i, row in enumerate(rows):
        for j in range(n):
            if row >> j & 1:
                downs[j] |= 1 << i
    table = [0] * (1 << n)
    for s in range(1, 1 << n):
        b = s & -s
        table[s] = table[s ^ b] | downs[b.bit_length() - 1]
    return table


def profile(target: int, full: int, closure: list[int], c: int) -> tuple[int, list[int]]:
    """Return N_c and F_0,...,F_{N_c}."""
    f = full
    chain = [f]
    i = 0
    seen: set[tuple[int, int]] = set()
    while f:
        state = (f, i % 2)
        if state in seen:
            raise RuntimeError('nonterminating closure sequence')
        seen.add(state)
        next_color = (c + i + 1) % 2
        color_set = target if next_color else full ^ target
        f = closure[f & color_set]
        chain.append(f)
        i += 1
    return i, chain


def alternating_profile(rows: tuple[int, ...], target: int) -> tuple[int, int]:
    n = len(rows)
    a = [1] * n
    maxima = [0, 0]
    for x in range(n):
        cx = target >> x & 1
        for y in range(x):
            if rows[y] >> x & 1 and (target >> y & 1) != cx:
                a[x] = max(a[x], a[y] + 1)
        maxima[cx] = max(maxima[cx], a[x])
    return 1 + maxima[1], 1 + maxima[0]


def minimax(target: int, full: int, opens: tuple[int, ...]) -> int:
    @lru_cache(None)
    def solve(state: int) -> int:
        if not state & target or not state & (full ^ target):
            return 0
        best = state.bit_count() - 1
        cuts = {state & u for u in opens}
        for a in cuts:
            if not a or a == state:
                continue
            value = 1 + max(solve(a), solve(state ^ a))
            best = min(best, value)
            if best == 1:
                break
        return best
    return solve(full)


def synthesize(full: int, chain: list[int], c: int, lo: int, hi: int) -> dict:
    """Balanced open-query tree for layer indices lo,...,hi-1."""
    if hi - lo == 1:
        return {'color': (c + lo) % 2, 'layer': lo}
    mid = (lo + hi) // 2
    return {'open_mask': full ^ chain[mid],
            'yes': synthesize(full, chain, c, lo, mid),
            'no': synthesize(full, chain, c, mid, hi)}


def run_tree(tree: dict, point: int) -> tuple[int, int]:
    depth = 0
    while 'color' not in tree:
        tree = tree['yes' if tree['open_mask'] >> point & 1 else 'no']
        depth += 1
    return tree['color'], depth


def write_tables(output: Path) -> None:
    with (output / 'ordinal_values.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['last_derivative_rank_h', 'sm_one_top_point',
                         'sm_at_least_two_top_points', 'duplication_jump'])
        for h in range(129):
            one = ceil_log2(h + 1)
            two = ceil_log2(h + 2)
            writer.writerow([h, one, two, two - one])
            assert (two - one == 1) == ((h + 1) & h == 0)
    with (output / 'sharp_family.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['k', 'ordinal_exponent_2_to_k_minus_1', 'sm_X', 'sm_double_X'])
        for k in range(1, 17):
            h = (1 << k) - 1
            assert ceil_log2(h + 1) == k
            assert ceil_log2(h + 2) == k + 1
            writer.writerow([k, h, k, k + 1])


def verify(max_n: int, output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    records = []
    total = 0
    t0 = perf_counter()
    for n in range(1, max_n + 1):
        count = targets = 0
        histogram: dict[int, int] = {}
        for rows in natural_posets(n):
            count += 1
            full = (1 << n) - 1
            opens = upsets(rows)
            close = closure_table(rows)
            worst = 0
            for target in range(1 << n):
                targets += 1
                n0, f0 = profile(target, full, close, 0)
                n1, f1 = profile(target, full, close, 1)
                assert (n0, n1) == alternating_profile(rows, target)
                predicted = ceil_log2(min(n0, n1))
                actual = minimax(target, full, opens)
                assert actual == predicted, (rows, target, actual, predicted)
                c, chain = (0, f0) if n0 <= n1 else (1, f1)
                tree = synthesize(full, chain, c, 0, len(chain) - 1)
                max_depth = 0
                for x in range(n):
                    color, depth = run_tree(tree, x)
                    assert color == target >> x & 1
                    max_depth = max(max_depth, depth)
                assert max_depth <= predicted
                worst = max(worst, actual)
            histogram[worst] = histogram.get(worst, 0) + 1
        total += targets
        records.append({'n': n, 'natural_posets': count, 'target_tests': targets,
                        'posets_by_sm': histogram})
        print(f'n={n}: {count} natural posets; {targets} targets; PASS', flush=True)
    write_tables(output)
    # Two oppositely coloured four-element chains: depth two becomes three.
    rows = tuple(sum(1 << j for j in range(i + 1, 4)) if i < 4
                 else sum(1 << j for j in range(i + 1, 8)) for i in range(8))
    target = sum(1 << i for i in (1, 3, 4, 6))
    full = 255
    close = closure_table(rows)
    n0, f0 = profile(target, full, close, 0)
    n1, _ = profile(target, full, close, 1)
    assert (n0, n1) == (5, 5)
    assert minimax(target, full, upsets(rows)) == 3
    certificate = {'description': 'Two opposite alternating four-element chains',
                   'strict_upper_rows': rows, 'target_mask': target,
                   'N_0': n0, 'N_1': n1, 'optimal_depth': 3,
                   'tree': synthesize(full, f0, 0, 0, n0)}
    (output / 'strategy_certificate.json').write_text(json.dumps(certificate, indent=2) + '\n')
    result = {'status': 'PASS', 'exhaustive_through_n': max_n,
              'total_target_tests': total, 'records': records,
              'additional_checks': ['opposite four-chains certificate',
                                    '129 finite-height formula rows',
                                    '16 sharp-family rows'],
              'elapsed_seconds': round(perf_counter() - t0, 3),
              'scope': 'Finite upper-set topologies only. Not a computer proof of the infinite-space theorems.'}
    (output / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    with (output / 'finite_poset_checks.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['n', 'natural_posets', 'target_tests'])
        writer.writerows((r['n'], r['natural_posets'], r['target_tests']) for r in records)
    print(f'PASS: {total} target tests; elapsed {result["elapsed_seconds"]}s', flush=True)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=5)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    if not 1 <= args.max_n <= 7:
        parser.error('--max-n must be between 1 and 7; exhaustive work grows rapidly')
    verify(args.max_n, args.output)


if __name__ == '__main__':
    main()
