#!/usr/bin/env python3
"""Exact finite checks for the binary orthogonal principal-nullity theorem.

Run with Python 3.10+ and no dependencies. The output is deterministic.
Vectors are binary integers; matrices are tuples of their column vectors.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import prod


def gaussian(n, k):
    """Number of k-dimensional subspaces of F_2^n."""
    if not 0 <= k <= n:
        return 0
    return prod(2**n - 2**i for i in range(k)) // prod(
        2**k - 2**i for i in range(k)
    )


def span(vectors):
    current = {0}
    for vector in vectors:
        current |= {x ^ vector for x in current}
    return frozenset(current)


def apply_matrix(columns, x):
    value = 0
    while x:
        low_bit = x & -x
        value ^= columns[low_bit.bit_length() - 1]
        x ^= low_bit
    return value


def binary_rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            p = vector.bit_length()
            if p not in pivots:
                pivots[p] = vector
                break
            vector ^= pivots[p]
    return len(pivots)


def gram(columns):
    return tuple(
        (columns[i] & columns[j]).bit_count() % 2
        for j in range(len(columns)) for i in range(j + 1)
    )


def orthogonal_group(n):
    """Enumerate orthonormal bases, independently of frame extension results."""
    odd_vectors = [x for x in range(1, 1 << n) if x.bit_count() % 2]

    def extend(prefix):
        if len(prefix) == n:
            yield prefix
        else:
            for y in odd_vectors:
                if all((y & x).bit_count() % 2 == 0 for x in prefix):
                    yield from extend(prefix + (y,))

    return list(extend(()))


def verify_orbits_and_complements():
    print("Orthogonal groups: order, maximum-nullity histogram, frame orbits")
    for n in range(2, 6):
        ones = (1 << n) - 1
        group = orthogonal_group(n)
        group_order = len(group)
        assert group_order == {2: 2, 3: 6, 4: 48, 5: 720}[n]
        histogram = Counter()
        for columns in group:
            assert apply_matrix(columns, ones) == ones
            nullities = {}
            for mask in range(1 << n):
                restricted = [column & mask for i, column in enumerate(columns)
                              if mask >> i & 1]
                nullities[mask] = len(restricted) - binary_rank(restricted)
            assert all(nullities[m] == nullities[ones ^ m] for m in nullities)
            histogram[max(nullities.values())] += 1

        frame_orbits = {}
        for k in range(1, min(3, n - 1) + 1):
            fibres = defaultdict(set)
            for frame in product(range(1, 1 << n), repeat=k):
                if binary_rank(frame + (ones,)) == k + 1:
                    fibres[gram(frame)].add(frame)
            for fibre in fibres.values():
                source = min(fibre)
                actual_orbit = {tuple(apply_matrix(q, x) for x in source)
                                for q in group}
                assert actual_orbit == fibre
            frame_orbits[k] = (len(fibres), sum(map(len, fibres.values())))
        print(f"n={n}: |O|={group_order}, nu={dict(sorted(histogram.items()))}, "
              f"k:(orbits,frames)={frame_orbits}")


def subspaces(mask, r):
    """Enumerate r-spaces supported on the coordinate set encoded by mask."""
    supported = [x for x in range(1, mask + 1) if x & mask == x]
    spaces = {span(basis) for basis in combinations(supported, r)
              if binary_rank(basis) == r}
    assert len(spaces) == gaussian(mask.bit_count(), r)
    return sorted(spaces, key=lambda space: tuple(sorted(space)))


def intersection_dimension(u, v):
    size = len(u & v)
    assert size & (size - 1) == 0
    return size.bit_length() - 1


def iid_exponent_checks():
    print("Independent square matrix: exact pair-of-witness probabilities")
    total = 0
    histograms_checked = 0
    for n, b, r in [(3, 2, 1), (4, 2, 1), (4, 2, 2), (5, 3, 1), (5, 3, 2)]:
        for t in range(max(0, 2*b - n), b + 1):
            # By coordinate symmetry only the overlap size matters.
            s_mask = (1 << b) - 1
            t_mask = ((1 << t) - 1) | (((1 << (b - t)) - 1) << b)
            left, right = subspaces(s_mask, r), subspaces(t_mask, r)
            intersections = Counter()
            for u_space in left:
                for v_space in right:
                    j = intersection_dimension(u_space, v_space)
                    intersections[j] += 1
                    # Count possible matrix rows directly by their dot products.
                    by_left = {x for x in range(1 << n)
                               if all(not ((x & y).bit_count() % 2) for y in u_space)}
                    by_right = {x for x in range(1 << n)
                                if all(not ((x & y).bit_count() % 2) for y in v_space)}
                    count = 1
                    for i in range(n):
                        in_s, in_t = (s_mask >> i) & 1, (t_mask >> i) & 1
                        if in_s and in_t:
                            count *= len(by_left & by_right)
                        elif in_s:
                            count *= len(by_left)
                        elif in_t:
                            count *= len(by_right)
                        else:
                            count *= 1 << n
                    assert count == 1 << (n*n - 2*b*r + t*j)
                    total += 1
            for d in range(r + 1):
                measured = Fraction(sum(c * gaussian(j, d)
                                        for j, c in intersections.items()),
                                    len(left) * len(right))
                predicted = gaussian(t, d) * Fraction(
                    gaussian(b - d, r - d), gaussian(b, r))**2
                assert measured == predicted
                histograms_checked += 1
    print(f"{total} witness-pair probabilities; {histograms_checked} "
          "Gaussian intersection moments")


def verify_gram_counts():
    """Dynamic counts by Gram and row span, retaining deficient frames too."""
    # Full column rank of [Z | 1] is equivalent to regularity of Z.
    print("Gram fibre estimates: all symmetric targets by exact row recursion")
    for d in range(1, 4):
        D = d * (d + 1) // 2
        row_types = []
        for x in range(1 << d):
            z = tuple((x >> j) & 1 for j in range(d))
            g = sum(bit << i for i, bit in enumerate(gram(z)))
            row_types.append((g, x | (1 << d)))

        counts = Counter({(0, frozenset({0})): 1})
        extended = {}
        for m in range(1, 2*d + 7):
            next_counts = Counter()
            for (g, row_span), multiplicity in counts.items():
                for contribution, row in row_types:
                    key = (row_span, row)
                    if key not in extended:
                        extended[key] = row_span | {v ^ row for v in row_span}
                    next_counts[g ^ contribution, extended[key]] += multiplicity
            counts = next_counts
            if m < 2*d + 5:
                continue
            unrestricted, regular = Counter(), Counter()
            for (g, row_span), multiplicity in counts.items():
                unrestricted[g] += multiplicity
                if len(row_span) == 1 << (d+1):
                    regular[g] += multiplicity
            total = 1 << (m*d)
            assert sum(unrestricted.values()) == total
            a = Fraction(1, 1 << (m - 2*d))
            low = min(Fraction((1 << D) * regular[g], total)
                      for g in range(1 << D))
            high = max(Fraction((1 << D) * unrestricted[g], total)
                       for g in range(1 << D))
            assert low >= 1 - Fraction(4, 3)*a
            assert high <= 1 / (1 - 4*a)
            print(f"d={d}, m={m}, {1 << D} targets: "
                  f"min scaled regular={low}, max scaled total={high}")


def exhaustive_second_moment():
    """Check both aggregate iid witness moments using every 4-by-4 matrix."""
    n, b, r = 4, 2, 1
    masks = [m for m in range(1 << n) if m.bit_count() == b]
    spaces = {m: subspaces(m, r) for m in masks}
    by_kernel = {h: gaussian(h, r) for h in range(b + 1)}
    total_x = total_x2 = 0
    for columns in product(range(1 << n), repeat=n):
        x = 0
        for mask in masks:
            rank = binary_rank(col & mask for i, col in enumerate(columns)
                               if mask >> i & 1)
            x += by_kernel[b - rank]
        total_x += x
        total_x2 += x*x
    measure = 1 << (n*n)
    predicted_mean = Fraction(len(masks) * gaussian(b, r), 1 << (b*r))
    predicted_second = sum(
        Fraction(1, 1 << (2*b*r - (m & k).bit_count()
                            * intersection_dimension(u, v)))
        for m in masks for k in masks for u in spaces[m] for v in spaces[k])
    assert Fraction(total_x, measure) == predicted_mean
    assert Fraction(total_x2, measure) == predicted_second
    print(f"All {measure} binary {n}x{n} matrices, b={b}, r={r}: "
          f"E[X]={predicted_mean}, E[X^2]={predicted_second}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so all exact checks execute.")
    verify_orbits_and_complements()
    iid_exponent_checks()
    verify_gram_counts()
    exhaustive_second_moment()
    print("All exact checks passed.")
