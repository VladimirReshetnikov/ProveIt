#!/usr/bin/env python3
"""Exact independent checks for four-step graph towers (Python standard library).

Run python verify.py to reproduce verification.txt. The --limit option extends
the prime range for the independent direct curve counts.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from math import comb, isqrt


def primes(limit):
    return [p for p in range(5, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def phi2(a, p):
    """Quadratic character of a, including value zero."""
    symbol = pow(a % p, (p - 1) // 2, p)
    return -1 if symbol == p - 1 else symbol


def elliptic_trace(p, root):
    return -sum(phi2(x * (x - 1) * (x - root), p) for x in range(p))


def elliptic_curve_count(p, twist):
    signs = [phi2(d, p) for d in twist]
    assert all(signs)
    pair_trace = sum(a * b for a, b in combinations(signs, 2))
    all_sign = signs[0] * signs[1] * signs[2] * signs[3]
    return (p + 1 - pair_trace * elliptic_trace(p, -2)
            - 3 * all_sign * elliptic_trace(p, 4))


def direct_curve_count(p, twist):
    """Count the individual vectors with both moments zero via pair tables."""
    def moments(a, b):
        first = [(a * x * x) % p for x in range(p)]
        second = [(b * x * x) % p for x in range(p)]
        return Counter(((s + t) % p, (s * s + t * t) % p)
                       for s in first for t in second)

    a, b, c, d = twist
    left = moments(a, b)
    right = left if (a, b) == (c, d) else moments(c, d)
    total = sum(m * right[(-s % p, -t % p)] for (s, t), m in left.items())
    assert (total - 1) % (p - 1) == 0
    return (total - 1) // (p - 1)


def orbit_residue(p):
    """Exceptional orbit counts on the untwisted curve, modulo 192."""
    root = next((d for d in range(p) if (d * d + 2) % p == 0), None)
    repeated = (root is not None and phi2(-1 + root, p) == 1
                and phi2(-1 - root, p) == 1)
    return 32 * (p % 3 == 1) + 48 * (p % 8 == 1) + 96 * repeated


def rref_planes(p):
    """All two-dimensional row spaces, in unique reduced echelon form."""
    for i, j in combinations(range(4), 2):
        free = ([(0, k) for k in range(i + 1, 4) if k != j]
                + [(1, k) for k in range(j + 1, 4)])
        for choices in product(range(p), repeat=len(free)):
            rows = [[0] * 4, [0] * 4]
            rows[0][i] = rows[1][j] = 1
            for (row, col), value in zip(free, choices):
                rows[row][col] = value
            yield tuple(rows[0]), tuple(rows[1])


def point_depths(p):
    """Compute all first nonzero even moments on normalized projective points."""
    values = [[pow(t, 2 * j, p) for t in range(p)] for j in range(1, 5)]
    result = {}
    for pivot in range(4):
        for tail in product(range(p), repeat=3 - pivot):
            point = (0,) * pivot + (1,) + tail
            result[point] = next(j for j, row in enumerate(values, 1)
                                 if sum(row[x] for x in point) % p)
    return result


def direct_distribution(p):
    depth = point_depths(p)
    hist = Counter()
    generator_types = Counter()
    for a, b in rref_planes(p):
        depths = [depth[b]]
        for t in range(p):
            point = tuple((x + t * y) % p for x, y in zip(a, b))
            depths.append(depth[point])
        hist[sum(depths) - (p + 1)] += 1
        if 1 not in depths:
            generator_types[(depths.count(3), depths.count(4))] += 1
    return hist, generator_types


def unordered_pairs(categories):
    """Histogram of sums of excess depths of distinct unordered point pairs."""
    result = Counter()
    for weight, count in categories.items():
        result[2 * weight] += comb(count, 2)
        for other, amount in categories.items():
            if other > weight:
                result[weight + other] += count * amount
    return result


def predicted_distribution(p):
    c = elliptic_curve_count(p, (1, 1, 1, 1))
    split = int(p % 8 == 1)
    deep = 48 * split
    pts = {1: (p + 1)**2 - c, 2: c - deep, 3: deep}
    types = {(0, 0): 2 * (p + 1) - 12 * split - c // 2,
             (4, 0): (c - deep) // 2,
             (0, 2): 24 * split,
             (0, 4): 12 * split}
    hist = unordered_pairs(pts)
    hist[0] += p**2 * (p - 1)**2 // 2
    for weight, count in pts.items():
        hist[weight] += (p - 1) * count
    for (b, d), nlines in types.items():
        categories = {1: p + 1 - b - d, 2: b, 3: d}
        for weight, pairs in unordered_pairs(categories).items():
            hist[weight] -= nlines * pairs
        hist[p + 1 + b + 2 * d] += nlines
    assert min(hist.values()) >= 0 and min(types.values()) >= 0
    assert sum(hist.values()) == (p**2 + 1) * (p**2 + p + 1)
    return +hist, +Counter(types)


def main(limit):
    print("Exact counts for Y_i = d_i X_i^2, sum Y_i = sum Y_i^2 = 0.")
    print("Prime  trace(E1)  trace(E2)  projective points (d_i=1)")
    for p in primes(limit):
        c = direct_curve_count(p, (1, 1, 1, 1))
        assert c == elliptic_curve_count(p, (1, 1, 1, 1))
        assert c % 192 == orbit_residue(p)
        print(f"{p:5d}  {elliptic_trace(p, -2):9d}  {elliptic_trace(p, 4):9d}  {c:17d}")
    print("All untwisted counts satisfy the exceptional-orbit congruence modulo 192.")
    print("\nQuadratic twists by 0, 1, 2 nonsquare coefficients (remaining d_i=1)")
    for p in (11, 13, 17, 19, 23, 31, 41):
        nonresidue = next(d for d in range(2, p) if phi2(d, p) == -1)
        counts = []
        for n in range(5):
            twist = (nonresidue,) * n + (1,) * (4 - n)
            c = direct_curve_count(p, twist)
            assert c == elliptic_curve_count(p, twist)
            counts.append(c)
        assert counts == counts[::-1]
        print(f"p={p:2d}  nonsquare={nonresidue}  counts={counts[:3]}")
    for p in (11, 13, 17):
        hist, generators = direct_distribution(p)
        assert (hist, generators) == predicted_distribution(p)
        print(f"\np={p}, {sum(hist.values())} row planes")
        print("  extra depth : number of planes")
        for size, count in sorted(hist.items()):
            print(f"  {size:11d} : {count}")
        print("  generator types (depth-three points, depth-four points) : count")
        for kind, count in sorted(generators.items()):
            print(f"  {kind} : {count}")
    print("\nAll direct enumerations agree with the formulas.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=200)
    main(parser.parse_args().limit)
