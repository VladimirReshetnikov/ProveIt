#!/usr/bin/env python3
"""Finite-rank illustration of the ambient branch construction.

This is NOT a finite model of T_cov and NOT a proof of the nonstandard theorem.
Every finite cutoff deliberately reports its missing predecessor boundary.
The main chain is unbounded; only finitely many sample inputs are inspected.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class Ambient:
    def __init__(self, join):
        self.join = join
        self.zero = (0, 0)
        self.one = (1, 0)

    def valid(self, x):
        n, label = x
        return n >= 0 and label >= 0 and (label == 0 or n < self.join)

    def successor(self, x):
        assert self.valid(x)
        n, label = x
        return (n + 1, label if label and n + 1 < self.join else 0)

    def delta(self, x, y):
        return self.zero if x == y else self.one

    def iterate(self, counter, seed, body):
        assert self.valid(counter) and self.valid(seed)
        state = seed
        for _ in range(counter[0]):
            state = body(state)
            assert self.valid(state)
        return state

    def retained(self, x, cutoff):
        return self.valid(x) and (x[1] == 0 or x[0] >= cutoff)

    def clock(self, x):
        return self.iterate(x, self.zero, self.successor)


def main():
    model = Ambient(12)
    samples = [(n, 0) for n in range(25)] + [
        (n, j) for n in range(12) for j in (1, 2, 3)]
    checks = 0
    boundary_rows = []
    for cutoff in (1, 4, 8):
        retained = [x for x in samples if model.retained(x, cutoff)]
        stop = (cutoff + 1, 1)
        bodies = [
            model.successor,
            lambda x: model.zero,
            lambda x: model.delta(x, model.zero),
            lambda x: model.iterate(model.delta(x, stop), x, model.successor),
            lambda x: model.delta(model.clock(x), x),
        ]
        for body in bodies:
            for seed in retained:
                assert model.iterate(model.zero, seed, body) == seed
                checks += 1
                for counter in retained:
                    left = model.iterate(model.successor(counter), seed, body)
                    right = body(model.iterate(counter, seed, body))
                    assert left == right
                    assert model.retained(left, cutoff)
                    checks += 1
        missing = [(cutoff, j) for j in (1, 2, 3)]
        for point in missing:
            predecessor = (cutoff - 1, point[1])
            assert model.successor(predecessor) == point
            assert not model.retained(predecessor, cutoff)
        boundary_rows.append({'cutoff': cutoff,
                              'explicit_coverage_failures': missing})
    left, right = (11, 0), (11, 1)
    assert left != right and model.successor(left) == model.successor(right)
    assert model.clock(model.zero) == model.zero
    for point in samples:
        assert model.clock(model.successor(point)) == model.successor(model.clock(point))
    assert model.clock(right) != right
    result = {
        'status': 'finite illustration only; every finite cutoff fails coverage',
        'join_rank': model.join,
        'sample_computation_and_lower_bound_checks': checks,
        'coverage_boundaries': boundary_rows,
        'successor_collision': {'left': left, 'right': right,
                                'common_successor': model.successor(left)},
        'failed_clock': {'argument': right, 'clock_value': model.clock(right)},
        'not_a_proof': 'Nonstandard arithmetic, the external cut, all-term constancy and bi-interpretability are established by the written proof, not this program.',
    }
    (ROOT / 'evidence/finite_shadow.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
