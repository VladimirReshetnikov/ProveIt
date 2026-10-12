"""Finite independent checks of the exact universal connected-tile cutoff.

Checks the sharp comb examples by an unrestricted augmenting-path min-cut
oracle and compares complete marked signatures for small random connected
tiles.  The signature operations enumerate explicit source colorings and do
not invoke a repetition-kernel producer.
"""
from __future__ import annotations

from collections import deque
from itertools import product
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'code')]
from pattern_kernel.core import Tile
from pattern_kernel.signatures import tile_table, power


def cutoff(k):
    return [1, 3, 4][k] if k < 3 else k + 1


def path_marked_minimum(length, endpoints):
    minimum = None
    for inner in product(range(2), repeat=length - 1):
        colors = (endpoints[0],) + inner + (endpoints[1],)
        flags = set()
        cost = 0
        for a, b in zip(colors, colors[1:]):
            if a != b:
                cost += 1
            else:
                flags.add(a)
        if flags == {0, 1}:
            minimum = cost if minimum is None else min(minimum, cost)
    return minimum


def comb_power(k, copies):
    """An explicit rectangular strip of the comb tile; no production assembly."""
    width = 2 * (k + 1)
    edges = []
    for layer in range(copies):
        offset = layer * width
        edges.extend((offset + i, offset + width + i) for i in range(width))
        edges.extend((offset + i, offset + i + 1) for i in range(width - 1))
    left = tuple(range(width))
    right = tuple(copies * width + i for i in range(width))
    return (copies + 1) * width, edges, left, right


def boundary_min_cut(n, edges, ones, zeros):
    """Elementary max-flow/min-cut oracle for a finite undirected graph."""
    source, sink = n, n + 1
    residual = [dict() for _ in range(n + 2)]

    def arc(a, b, value):
        residual[a][b] = residual[a].get(b, 0) + value
        residual[b].setdefault(a, 0)

    for a, b in edges:
        if a != b:
            arc(a, b, 1)
            arc(b, a, 1)
    large = len(edges) + 1
    for a in ones:
        arc(source, a, large)
    for a in zeros:
        arc(a, sink, large)
    value = 0
    while True:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            a = queue.popleft()
            for b, capacity in residual[a].items():
                if capacity > 0 and b not in parent:
                    parent[b] = a
                    queue.append(b)
        if sink not in parent:
            shore = set(parent)
            break
        amount = large
        b = sink
        while b != source:
            a = parent[b]
            amount = min(amount, residual[a][b])
            b = a
        b = sink
        while b != source:
            a = parent[b]
            residual[a][b] -= amount
            residual[b][a] += amount
            b = a
        value += amount
    if not set(ones) <= shore or set(zeros) & shore:
        raise AssertionError('minimum cut violated fixed boundary colors')
    cut = sum((a in shore) != (b in shore) for a, b in edges)
    if cut != value:
        raise AssertionError('flow value and residual cut do not agree')
    return value


def main():
    small = {
        'threshold_one_two_edges': path_marked_minimum(2, (0, 1)),
        'threshold_one_three_edges': path_marked_minimum(3, (0, 1)),
        'threshold_two_three_edges': path_marked_minimum(3, (0, 0)),
        'threshold_two_four_edges': path_marked_minimum(4, (0, 0)),
    }
    if list(small.values()) != [None, 1, None, 2]:
        raise AssertionError('single-edge sharp examples failed')

    combs = []
    for k in range(3, 17):
        minima = []
        for copies in [k, k + 1]:
            n, edges, left, right = comb_power(k, copies)
            boundary_one = left[:k + 1] + right[:k + 1]
            boundary_zero = left[k + 1:] + right[k + 1:]
            minima.append(boundary_min_cut(n, edges, boundary_one, boundary_zero))
            if copies == k:
                colors = [(v % (2 * (k + 1))) < k + 1 for v in range(n)]
                cut_cost = sum(colors[a] != colors[b] for a, b in edges)
                marks = {colors[a] for a, b in edges if colors[a] == colors[b]}
                if cut_cost != k or marks != {False, True}:
                    raise AssertionError('explicit sharp comb coloring failed')
        if minima != [k, k + 1]:
            raise AssertionError(('comb min-cuts differ', k, minima))
        combs.append({'threshold': k, 'width': 2 * (k + 1),
                      'min_cut_at_k_copies': minima[0],
                      'min_cut_at_k_plus_one_copies': minima[1]})

    seed = 20610317
    rng = random.Random(seed)
    comparisons = 0
    entries = 0
    for trial in range(64):
        width = 1 + trial % 2
        n = 2 * width + rng.randrange(3)
        order = list(range(n))
        rng.shuffle(order)
        edges = [(order[i], order[rng.randrange(i)]) for i in range(1, n)]
        edges.extend((rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(4)))
        rng.shuffle(order)
        tile = Tile(n, tuple(edges), tuple(order[:width]), tuple(order[width:2 * width]))
        for k in range(8):
            b = cutoff(k)
            table = tile_table(tile, k)
            expected = power(table, b, k)
            for copies in [b + 1, b + 2, 2 * b + 3, 2 * b + 11]:
                if power(table, copies, k) != expected:
                    raise AssertionError(('complete signature mismatch', trial, k, copies))
                comparisons += 1
                entries += 4 * (1 << (2 * width))

    report = {
        'all_passed': True,
        'claimed_exact_cutoff': {'0': 1, '1': 3, '2': 4, 'k>=3': 'k+1'},
        'single_edge_sharpness': small,
        'sharp_comb_examples': combs,
        'random_seed': seed,
        'random_connected_tiles': 64,
        'thresholds_checked': list(range(8)),
        'complete_signature_comparisons': comparisons,
        'signature_entries_compared': entries,
        'production_general_cutoff_modified': True,
    }
    text = json.dumps(report, indent=2) + '\n'
    (ROOT / 'results' / 'connected_cutoff_audit.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
