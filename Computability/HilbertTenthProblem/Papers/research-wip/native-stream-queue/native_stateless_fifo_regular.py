#!/usr/bin/env python3
"""Exact finite checks for the stateless constant-length FIFO theorem.

The general regular-language conclusion is proved in the adjacent note.
Finite graph checks are independent of the selector or Pell implementations.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def compose(left, right):
    """Relations carry sets of accumulated finite OR flags."""
    n = len(left)
    out = [[set() for _ in range(n)] for _ in range(n)]
    for a, b, c in product(range(n), repeat=3):
        for u, v in product(left[a][b], right[b][c]):
            out[a][c].add(u | v)
    return tuple(tuple(frozenset(s) for s in row) for row in out)


def identity(n):
    return tuple(tuple(frozenset({0}) if a == b else frozenset()
                       for b in range(n)) for a in range(n))


def adjacency(n, edges):
    out = [[set() for _ in range(n)] for _ in range(n)]
    for a, b, flag in edges:
        out[a][b].add(flag)
    return tuple(tuple(frozenset(s) for s in row) for row in out)


def powers_and_period(n, edges):
    base = adjacency(n, edges)
    seq, seen = [], {}
    current = identity(n)
    while current not in seen:
        seen[current] = len(seq)
        seq.append(current)
        current = compose(current, base)
    start = seen[current]
    return seq, start, len(seq)-start


def power(seq, start, period, exponent):
    if exponent >= len(seq):
        exponent = start+(exponent-start) % period
    return seq[exponent]


def round_masks(initial, steps, first, power_at):
    """Exact masks of zero-reaching runs with a prescribed first edge."""
    assert steps >= 1
    m = len(initial)
    h, p = divmod(steps, m)
    source, target, flag = first
    if initial[0] != source:
        return set()
    masks = {0}
    for j, value in enumerate(initial):
        count = h+int(j < p)
        if j == 0:
            assert count >= 1
            options = {flag | z for z in power_at(count-1)[target][0]}
        else:
            options = power_at(count)[value][0]
        masks = {a | b for a, b in product(masks, options)}
    return masks


def fifo_masks(initial, limit, edges):
    """Direct queue execution; no round-count formula is used here."""
    first = edges[0]
    source, target, flag = first
    states = {(initial[1:]+(target,), flag)} if initial[0] == source else set()
    result = []
    for time in range(1, limit+1):
        result.append({mask for queue, mask in states if not any(queue)})
        states = {(queue[1:]+(b,), mask | f)
                  for queue, mask in states for a, b, f in edges
                  if queue[0] == a}
    return result


def check():
    graph_count = comparisons = periodic_checks = accepted = 0
    max_preperiod = max_period = 0
    # All ordered three-edge graphs on three vertices, including duplicates.
    # Flags record a nonzero read and a nonzero append; this exercises the
    # finite-mask treatment of additional positive stream requirements.
    available = [(a, b, int(a != 0)+2*int(b != 0))
                 for a, b in product(range(3), repeat=2)]
    words = [(1, 2), (0, 1, 2), (1, 0, 2), (1, 1, 2)]
    for edges in product(available, repeat=3):
        seq, start, period = powers_and_period(3, edges)
        base = adjacency(3, edges)
        at = lambda k: power(seq, start, period, k)
        # Independent direct multiplication past both the first repeat and
        # two subsequent periods checks the eventual-power lookup.
        actual = identity(3)
        for k in range(len(seq)+2*period+2):
            assert actual == at(k)
            actual = compose(actual, base)
            periodic_checks += 1
        for initial in words:
            direct = fifo_masks(initial, 12, edges)
            for t, expected in enumerate(direct, 1):
                observed = round_masks(initial, t, edges[0], at)
                assert observed == expected, (edges, initial, t, observed, expected)
                comparisons += 1
                accepted += bool(observed)
        graph_count += 1
        max_preperiod = max(max_preperiod, start)
        max_period = max(max_period, period)
    return dict(status='PASS_STATELESS_FIFO_ROUND_DECOMPOSITION',
                graphs=graph_count, arbitrary_duration_comparisons=comparisons,
                zero_reaching_cases=accepted, repeated_power_checks=periodic_checks,
                maximum_preperiod=max_preperiod, maximum_period=max_period,
                scope='Exhaustive finite three-vertex checks with global OR flags; '
                      'general regularity is a mathematical proof, not a finite test.',
                established_complete_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = check()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result
    print(json.dumps(result, indent=2))
