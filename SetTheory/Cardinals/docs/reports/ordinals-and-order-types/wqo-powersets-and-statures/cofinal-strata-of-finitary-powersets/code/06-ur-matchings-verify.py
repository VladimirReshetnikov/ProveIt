#!/usr/bin/env python3
"""Exhaustive and seeded checks. Finite tests are not transfinite proofs."""
from __future__ import annotations
import copy
import itertools
import json
import random
import sys
import time
from collections import Counter
from functools import lru_cache
from pathlib import Path
from ordinal_matchings import (Instance, solve, check_certificate, compress_twins,
                               enumerate_matchings, triangular_order, solve_by_covered_rows)

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter[str] = Counter()


def expect(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    COUNTS[category] += 1


def normalize_word(word: list[int]) -> tuple[tuple[int, int], ...]:
    """Independent right-to-left CNF normalization, not the production adder."""
    largest = 0
    counts: Counter[int] = Counter()
    for exponent in reversed(word):
        if exponent and exponent >= largest:
            counts[exponent] += 1
            largest = exponent
    return tuple(sorted(counts.items(), reverse=True))


def brute_permutations(inst: Instance) -> tuple[tuple[int, int], ...]:
    best = ()
    for order in itertools.permutations(range(inst.upper_count)):
        positions = {u: i for i, u in enumerate(order)}
        group_max = [0] * inst.upper_count
        for mask, priority in zip(inst.row_masks, inst.priorities):
            first = min(positions[u] for u in range(inst.upper_count) if mask >> u & 1)
            group_max[first] = max(group_max[first], priority)
        value = normalize_word(group_max + [inst.terminal])
        best = max(best, value)
    return best


def brute_ordered_matchings(inst: Instance) -> tuple[tuple[int, int], ...]:
    best = ((inst.terminal, 1),)
    for matching in enumerate_matchings(inst):
        for edges in itertools.permutations(matching):
            if all(not inst.row_masks[ell] >> v & 1
                   for i, (ell, _) in enumerate(edges) for _, v in edges[:i]):
                value = normalize_word([inst.priorities[ell] for ell, _ in edges]
                                       + [inst.terminal])
                best = max(best, value)
    return best


def layer_solver(inst: Instance) -> tuple[tuple[int, int], ...]:
    """Independent maximum-UR-matching priority recurrence from the article."""
    @lru_cache(None)
    def rec(rows: tuple[int, ...], priorities: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
        peak = max(priorities, default=0)
        if peak < inst.terminal:
            return ((inst.terminal, 1),)
        H = [i for i, p in enumerate(priorities) if p == peak]
        high = Instance(tuple(rows[i] for i in H), (peak,) * len(H),
                        inst.upper_count, inst.terminal)
        maximum, masks = -1, set()
        for matching in enumerate_matchings(high):
            if triangular_order(high, matching) is not None:
                k = len(matching)
                mask = sum(1 << u for _, u in matching)
                if k > maximum:
                    maximum, masks = k, {mask}
                elif k == maximum:
                    masks.add(mask)
        if peak == inst.terminal:
            return ((peak, maximum + 1),)
        tails = []
        for selected in masks:
            expect(all(rows[i] & selected for i in H), 'maximum_high_matching_covers_high_rows')
            remaining = [i for i, p in enumerate(priorities)
                         if p < peak and not rows[i] & selected]
            tails.append(rec(tuple(rows[i] for i in remaining),
                             tuple(priorities[i] for i in remaining)))
        return ((peak, maximum),) + max(tails)
    return rec(inst.row_masks, inst.priorities)


def closure_height(inst: Instance) -> int:
    neighbourhoods = []
    for subset in range(1 << inst.upper_count):
        neighbourhoods.append(sum(1 << i for i, mask in enumerate(inst.row_masks) if mask & subset))
    family = sorted(set(neighbourhoods), key=lambda x: (x.bit_count(), x))
    heights = {}
    for covered in family:
        heights[covered] = 1 + max((value for smaller, value in heights.items()
                                   if smaller != covered and not smaller & ~covered), default=0)
    return max(heights.values())


def full_check(inst: Instance, matchings: bool = True) -> None:
    cert = solve(inst)
    value = tuple(tuple(t) for t in cert['value'])
    expect(check_certificate(inst, cert), 'certificate_checks')
    expect(value == brute_permutations(inst), 'dp_vs_all_permutations')
    expect(value == solve_by_covered_rows(inst), 'dp_vs_covered_rows')
    if matchings:
        expect(value == brute_ordered_matchings(inst), 'dp_vs_all_ordered_matchings')
        expect(value == layer_solver(inst), 'dp_vs_priority_layers')
    expect(value == tuple(solve(compress_twins(inst))['value']), 'twin_compression')


def examples() -> None:
    inputs = {
        'antichain': {'upper_count': 0, 'neighbours': [], 'priorities': [], 'terminal': 3},
        'single_edge': {'upper_count': 1, 'neighbours': [[0]], 'priorities': [1], 'terminal': 1},
        'six_cycle': {'upper_count': 3, 'neighbours': [[0, 1], [1, 2], [0, 2]], 'priorities': [1, 1, 1], 'terminal': 1},
        'weighted_cycle': {'upper_count': 3, 'neighbours': [[0, 1], [1, 2], [0, 2]], 'priorities': [3, 2, 1], 'terminal': 1},
        'forced_absorption': {'upper_count': 2, 'neighbours': [[0], [0, 1]], 'priorities': [2, 1], 'terminal': 1},
        'tie_requires_lookahead': {'upper_count': 2, 'neighbours': [[0, 1], [0]], 'priorities': [3, 2], 'terminal': 1},
        'terminal_absorption': {'upper_count': 2, 'neighbours': [[0], [1]], 'priorities': [1, 2], 'terminal': 3},
        'weighted_twins': {'upper_count': 4, 'neighbours': [[0, 1], [0, 1], [2, 3], [2, 3]], 'priorities': [1, 4, 2, 3], 'terminal': 1},
        'parallel_edges': {'upper_count': 3, 'neighbours': [[0], [1], [2]], 'priorities': [3, 1, 2], 'terminal': 1},
    }
    summary = {}
    for name, data in inputs.items():
        inst = Instance.from_dict(data)
        cert = solve(inst)
        full_check(inst)
        (ROOT / 'examples' / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
        (ROOT / 'examples' / (name + '_certificate.json')).write_text(json.dumps(cert, indent=2) + '\n')
        summary[name] = {'value': cert['value'], 'text': cert['value_text'], 'order': cert['order']}
        corrupted = copy.deepcopy(cert)
        corrupted['value'] = [[inst.terminal, 999]]
        try:
            check_certificate(inst, corrupted)
        except ValueError:
            COUNTS['tamper_rejections'] += 1
        else:
            raise AssertionError('Tampered terminal value accepted.')
    (ROOT / 'data' / 'examples_summary.json').write_text(json.dumps(summary, indent=2) + '\n')


def main() -> None:
    started = time.perf_counter()
    instances = 0
    for s in range(4):
        for r in range(4):
            for rows in itertools.product(range(1, 1 << s), repeat=r):
                for ps in itertools.product((1, 2, 3), repeat=r):
                    for tau in (1, 2, 3):
                        full_check(Instance(rows, ps, s, tau))
                        instances += 1
                uniform = Instance(rows, (1,) * r, s, 1)
                k = max((len(m) for m in enumerate_matchings(uniform)
                         if triangular_order(uniform, m) is not None), default=0)
                expect(closure_height(uniform) == k + 1, 'closure_lattice_height_vs_urm')
    print(f'Exhaustive weighted instances: {instances}', flush=True)
    uniform4 = 0
    for rows in itertools.product(range(1, 16), repeat=4):
        inst = Instance(rows, (1, 1, 1, 1), 4, 1)
        expect(tuple(solve(inst)['value']) == brute_permutations(inst), 'uniform_4x4_dp_vs_permutations')
        uniform4 += 1
    print(f'Exhaustive uniform 4x4 instances: {uniform4}', flush=True)
    rng = random.Random(20260929)
    for _ in range(120):
        r, s = rng.randint(1, 5), rng.randint(1, 5)
        inst = Instance(tuple(rng.randrange(1, 1 << s) for _ in range(r)),
                        tuple(rng.choice((1, 2, 5, 9, 10**12)) for _ in range(r)),
                        s, rng.choice((1, 3, 8)))
        full_check(inst)
    examples()
    for invalid in [
        {'upper_count': 1, 'neighbours': [[]], 'priorities': [1], 'terminal': 1},
        {'upper_count': 1, 'neighbours': [[0, 0]], 'priorities': [1], 'terminal': 1},
        {'upper_count': 1, 'neighbours': [[2]], 'priorities': [1], 'terminal': 1},
        {'upper_count': 1, 'neighbours': [[0]], 'priorities': [0], 'terminal': 1},
        {'upper_count': 1, 'neighbours': [[0]], 'priorities': [True], 'terminal': 1},
    ]:
        try:
            Instance.from_dict(invalid)
        except ValueError:
            COUNTS['invalid_input_rejections'] += 1
        else:
            raise AssertionError('Invalid input accepted.')
    result = {'status': 'PASS', 'seed': 20260929, 'python': sys.version.split()[0],
              'exhaustive_weighted_instances': instances,
              'exhaustive_uniform_4x4_instances': uniform4,
              'seeded_weighted_instances': 120, 'examples': 9,
              'assertions': dict(sorted(COUNTS.items())),
              'total_assertions': sum(COUNTS.values()),
              'elapsed_seconds': round(time.perf_counter() - started, 3),
              'scope': 'Finite algorithmic tests only; not a proof assistant check or novelty certification.'}
    (ROOT / 'data' / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
