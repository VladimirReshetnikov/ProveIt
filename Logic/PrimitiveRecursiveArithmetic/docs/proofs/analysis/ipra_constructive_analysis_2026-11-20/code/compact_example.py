"""Exact-rational regression checks for the compressed Lipschitz-function net.

Run with Python 3.10+; uses only the standard library.
"""
from fractions import Fraction as Q
from itertools import product


def snake(dimension, intervals):
    """List grid multi-indices with consecutive indices one edge apart."""
    indices = [()]
    for _ in range(dimension):
        previous = indices
        indices = []
        for j in range(intervals + 1):
            layer = previous if j % 2 == 0 else reversed(previous)
            indices.extend((j, *tail) for tail in layer)
    return indices


def clip(x, lo, hi):
    return max(lo, min(x, hi))


def round_nearest(x):
    return (x + Q(1, 2)) // 1


def encode(samples):
    return samples[0], [b - a for a, b in zip(samples, samples[1:])]


def decode(root, steps):
    values = [root]
    for step in steps:
        assert step in (-1, 0, 1)
        values.append(values[-1] + step)
    return values


def dist(x, y):
    return max(abs(a - b) for a, b in zip(x, y))


def center(x, vertices, data, value_step, lip, bound):
    value = min(z * value_step + lip * dist(x, v) for v, z in zip(vertices, data))
    return clip(value, -bound, bound)


def check_edges():
    # Both samples have common denominator D in units of delta.
    checked = 0
    for den in range(1, 16):
        for x in range(-4 * den, 4 * den + 1):
            for y in range(x - 3 * den // 4, x + 3 * den // 4 + 1):
                if 4 * abs(x - y) <= 3 * den:
                    assert abs(round_nearest(Q(x, den)) - round_nearest(Q(y, den))) <= 1
                    checked += 1
    return checked


def check_selected_centers():
    checks = 0
    for d, k, lip, scale in [(1, 0, Q(0), 0), (1, 2, Q(1), 0),
                             (1, 1, Q(3, 2), 1), (2, 0, Q(1), 0)]:
        bound = 1
        delta = Q(1, 2**(k + 2))
        intervals = 2**(k + 3 + scale)
        vertices = [tuple(Q(i, intervals) for i in v) for v in snake(d, intervals)]
        assert len(set(vertices)) == (intervals + 1)**d
        assert all(dist(x, y) == Q(1, intervals) for x, y in zip(vertices, vertices[1:]))
        for phase in [Q(-1), Q(1, 5), Q(1)]:
            def target(x):
                return clip(phase + lip * max(x), -bound, bound)
            samples = [
                round_nearest(clip(target(x) + (-1)**i * delta/8, -bound, bound) / delta)
                for i, x in enumerate(vertices)
            ]
            data = decode(*encode(samples))
            assert data == samples
            for x in product((Q(j, 9) for j in range(10)), repeat=d):
                error = abs(center(x, vertices, data, delta, lip, bound) - target(x))
                assert error <= 5 * delta / 8 + 2 * lip / intervals
                checks += 1
    return checks


def check_packing():
    # All sixteen masks for d=2,k=4 (four independent bumps).
    k, d = 4, 2
    eps = Q(1, 2**k)
    sites = list(product([Q(0), 8*eps], repeat=d))
    patterns = set()
    for mask in range(2**len(sites)):
        peaks = [c for i, c in enumerate(sites) if mask >> i & 1]
        def bump(x):
            return max([Q(0)] + [3*eps - dist(x, c) for c in peaks])
        pattern = sum(1 << i for i, c in enumerate(sites) if bump(c) > 3*eps/2)
        assert pattern == mask
        patterns.add(pattern)
    assert len(patterns) == 2**len(sites)
    return len(patterns)


if __name__ == "__main__":
    print(f"Quantized edge inequalities checked: {check_edges()}")
    print(f"Envelope evaluations checked: {check_selected_centers()}")
    print(f"Distinct decoded bump patterns checked: {check_packing()}")
