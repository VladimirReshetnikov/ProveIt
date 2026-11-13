"""Finite semantic falsification of direct computation leaves.

This is diagnostic evidence only. The independent sorted numerical decoder
checks ordinary natural-number denotations; the universal result is the
written semantic proof. Resource-limited cases are reported, not validated.
"""
import itertools
import json
import random
from pathlib import Path


def opener(a, t=None, d=0, k=-1):
    if type(a) is list:
        return [opener(b, t, d + 5 - len(a), k) for b in a]
    if type(a) is not int:
        raise ValueError('missing image')
    if k <= a < d:
        return a
    return opener(t, None, 3, k) if d % 2 else 0


class Limit(Exception):
    pass


def numerical(a, env=(), parameter=0, budget=None):
    if budget is None:
        budget = [20000]
    budget[0] -= 1
    if budget[0] < 0:
        raise Limit()
    if type(a) is int:
        if a < 0:
            assert a == -1
            return parameter
        return 0 if a < 3 else env[(a - 3) // 2]
    arity = len(a)
    if arity == 1:
        return 1 + numerical(a[0], (0, 0) + env, parameter, budget)
    if arity == 3:
        n = numerical(a[0], (0,) + env, parameter, budget)
        v = numerical(a[1], (0,) + env, parameter, budget)
        if n > budget[0]:
            raise Limit()
        for _ in range(n):
            v = numerical(a[2], (v,) + env, parameter, budget)
        return v
    return 0


def main():
    pool = list(range(-1, 10)) + [[], [0], [3], [5], [7],
        [[0]], [[5]], [0, 0], [0, 0, 3], [0, 0, 5], [0, [0], [7]],
        [0, [3], [9]], [0, 0, 0, 0], [0] * 6]
    attempted = admitted = checked = limited = 0
    rng = random.Random(20261112)
    cases = list(itertools.product(pool, repeat=3))
    for _ in range(30000):
        r = [rng.choice(pool) for _ in range(3)]
        index = rng.randrange(3)
        r[index] = [rng.choice(pool) for _ in range(rng.randrange(7))]
        cases.append(tuple(r))
    for s, u, t in cases:
        attempted += 1
        try:
            a = [[s and [s], u, t], opener(t, [s, u, t], 3) if s else u]
            opener(a)
        except (ValueError, RecursionError):
            continue
        admitted += 1
        for parameter in (0, 1, 2, 5):
            try:
                left = numerical(a[0], parameter=parameter)
                right = numerical(a[1], parameter=parameter)
            except Limit:
                limited += 1
                continue
            assert left == right, (s, u, t, parameter, a, left, right)
            checked += 1
    report = {'attempted_raw_packets': attempted,
              'scope_admitted_leaves': admitted,
              'semantic_instances_checked': checked,
              'resource_limited_instances': limited,
              'mismatches': 0,
              'parameter_values': [0, 1, 2, 5],
              'method': 'finite independent sorted-decoder falsification',
              'universal_proof': False}
    (Path(__file__).resolve().parents[1] / 'evidence' / 'compute_leaf_checks.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
