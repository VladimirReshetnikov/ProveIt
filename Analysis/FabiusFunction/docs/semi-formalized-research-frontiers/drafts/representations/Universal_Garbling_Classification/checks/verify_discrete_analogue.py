#!/usr/bin/env python3
"""Exact regression for a finite analogue, not a proof of the continuous theorem.

Reconstruct the only possible universal kernel for truncated geometric laws by
the first A total-sum equations. Check every remaining equation, stochasticity,
threshold identities, and identities after independent nontrivial noise.
Only Python's standard library is needed.
"""
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import json


def geometric(n, q):
    weights = [q**j for j in range(n)]
    return [v / sum(weights) for v in weights]


def candidate(px, py):
    a, b = len(px), len(py)
    k = [[F(0) for _ in range(b)] for _ in range(a)]
    for x in range(a):
        for y in range(b):
            rhs = py[y] * px[x-y] if 0 <= x-y < a else F(0)
            rhs -= sum(px[i]*py[x-i]*k[i][y]
                       for i in range(x) if 0 <= x-i < b)
            k[x][y] = rhs / (px[x]*py[0])
    return k


def joint_residual(px, py, k):
    a, b = len(px), len(py)
    result = {}
    for s in range(a+b-1):
        for y in range(b):
            lhs = sum(px[x]*py[s-x]*k[x][y]
                      for x in range(a) if 0 <= s-x < b)
            rhs = py[y]*px[s-y] if 0 <= s-y < a else F(0)
            result[s, y] = lhs-rhs
    return result


def main():
    noise = {-2: F(1, 5), 0: F(3, 10), 3: F(1, 2)}
    counts = dict(cases=0, feasible=0, infeasible=0, joint_equations=0,
                  noisy_equations=0, threshold_equations=0)
    examples = []
    for a in range(2, 10):
        for b in range(2, 10):
            for qx in (F(1, 2), F(1), F(2)):
                for qy in (F(1, 2), F(1), F(2)):
                    px, py = geometric(a, qx), geometric(b, qy)
                    k = candidate(px, py)
                    res = joint_residual(px, py, k)
                    stochastic = all(sum(row) == 1 and min(row) >= 0 for row in k)
                    feasible = stochastic and not any(res.values())
                    expected = qx == qy and a % b == 0
                    assert feasible == expected, (a, b, qx, qy)
                    counts['cases'] += 1
                    counts['feasible' if feasible else 'infeasible'] += 1
                    counts['joint_equations'] += len(res)
                    noisy = defaultdict(F)
                    for (s, y), v in res.items():
                        for z, pz in noise.items():
                            noisy[s+z, y] += pz*v
                    assert bool(any(noisy.values())) == bool(any(res.values()))
                    counts['noisy_equations'] += len(noisy)
                    if feasible:
                        assert all(k[x][y] == int(y == x % b)
                                   for x in range(a) for y in range(b))
                        for y in range(b):
                            cumulative = F(0)
                            for s in range(-2, a+b+2):
                                cumulative += noisy[s, y]
                                assert cumulative == 0
                                counts['threshold_equations'] += 1
                        if qx == 1:
                            examples.append(dict(source_points=a, target_points=b,
                                                 map=[x % b for x in range(a)]))
    result = dict(status='passed', arithmetic='exact rational',
                  scope='Finite truncated-geometric regression only; continuous theorem is proved analytically.',
                  counts=counts, uniform_examples=examples)
    out = Path(__file__).with_name('discrete_analogue_results.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['counts'], sort_keys=True))


if __name__ == '__main__':
    main()
