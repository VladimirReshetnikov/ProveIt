#!/usr/bin/env python3
"""Exact finite checks for local Euler-factor agreement of character packets.

A dual vector v reports the exponents a dot v modulo p for a in the packet.
The multiplicities of those exponents completely determine the local polynomial.
Only the Python standard library is required.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product


def projection(packet, v, p):
    return tuple(sorted((a * v[0] + b * v[1]) % p for a, b in packet))


def projective_vectors(p):
    return [(1, s) for s in range(p)] + [(0, 1)]


def normalize(x, y, p):
    """Return the standard projective representative of a nonzero vector."""
    if x % p:
        return (1, (y * pow(x % p, -1, p)) % p)
    assert y % p
    return (0, 1)


def cross_directions(A, B, p):
    return {normalize(a[0] - b[0], a[1] - b[1], p) for a in A for b in B}


def min_count(p, k):
    """Lower bound on the number of disagreeing vectors in a rank-two space."""
    return (p - 1) * (p + 1 - k)


def good_directions(A, B, p):
    return {v for v in projective_vectors(p) if projection(A, v, p) == projection(B, v, p)}


def cancel(A, B):
    a, b = Counter(A), Counter(B)
    return tuple((a - b).elements()), tuple((b - a).elements())


def check_net(A, B, good, p):
    """Confirm incidence one point of each color per occupied parallel line."""
    assert len(A) == len(B) == len(good)
    assert len(set(A) | set(B)) == 2 * len(A)
    directions = cross_directions(A, B, p)
    assert directions == {normalize(-v[1], v[0], p) for v in good}
    for v in good:
        left = projection(A, v, p)
        right = projection(B, v, p)
        assert left == right and len(set(left)) == len(A)


def full_parallel_lines(A, B, p):
    if len(A) != p or len(set(A) | set(B)) != 2 * p:
        return False
    return any(len(set(projection(A, v, p))) == len(set(projection(B, v, p))) == 1
               for v in projective_vectors(p))


def parallel_flats_plane(A, B, p):
    """Nonempty disjoint affine flats with the same translation space in F_p^2."""
    if len(A) != len(set(A)) or len(B) != len(set(B)):
        return False
    if len(A) == len(B) == 1:
        return True
    return full_parallel_lines(A, B, p)


def is_second_mass_shape(A, B, p):
    """The two reduced quotient shapes, checked here in rank two.

    A nontrivial period leaves quotient dimension at most one, where neither shape occurs.
    Both shapes in the plane have distinct entries within each packet.
    """
    m = len(A)
    if len(set(A) | set(B)) != 2 * m:
        return False
    if m == 2:
        same_center = all((sum(a[i] for a in A) - sum(b[i] for b in B)) % p == 0
                          for i in (0, 1))
        dx = ((A[0][0] - A[1][0]) % p, (A[0][1] - A[1][1]) % p)
        dy = ((B[0][0] - B[1][0]) % p, (B[0][1] - B[1][1]) % p)
        return same_center and (dx[0]*dy[1] - dx[1]*dy[0]) % p != 0
    if m != p - 1:
        return False
    normals_A = {v for v in projective_vectors(p) if len(set(projection(A, v, p))) == 1}
    normals_B = {v for v in projective_vectors(p) if len(set(projection(B, v, p))) == 1}
    if not normals_A or not normals_B or normals_A == normals_B:
        return False
    u, v = next(iter(normals_A)), next(iter(normals_B))
    # The missing point of each punctured line must be their common intersection.
    return (projection(A[:1], u, p)[0] not in projection(B, u, p)
            and projection(B[:1], v, p)[0] not in projection(A, v, p))


def check_mass(bad, A, B, p):
    """Return whether the sharp mass bound is attained after cancellation."""
    m = len(A)
    assert m == len(B)
    # Here delta = bad/p^2. Cross multiplication avoids floating-point rounding.
    lhs, rhs = bad * m, p * (p - 1)
    assert lhs >= rhs
    equal = lhs == rhs
    assert equal == parallel_flats_plane(A, B, p)
    assert equal or p * lhs >= 2 * (p - 1) * rhs
    assert (p * lhs == 2 * (p - 1) * rhs) == is_second_mass_shape(A, B, p)
    return equal


def exhaustive(p, k):
    points = tuple(product(range(p), repeat=2))
    vectors = projective_vectors(p)
    packets = list(combinations_with_replacement(points, k))
    profiles = [tuple(projection(A, v, p) for v in vectors) for A in packets]
    densities = Counter()
    for i, j in combinations(range(len(packets)), 2):
        A, B = packets[i], packets[j]
        good = {v for v, left, right in zip(vectors, profiles[i], profiles[j]) if left == right}
        # Every nonzero scalar multiple has the same agreement decision.
        bad = (p - 1) * (p + 1 - len(good))
        densities[bad] += 1
        left, right = cancel(A, B)
        m = len(left)
        assert m == len(right) and bad >= min_count(p, m) >= min_count(p, k)
        check_mass(bad, left, right, p)
        # An independent incidence criterion uses the original packets, not their projections.
        is_net = (len(set(A) | set(B)) == 2 * k and len(cross_directions(A, B, p)) == k
                  and all(len(cross_directions((a,), B, p)) == k for a in A)
                  and all(len(cross_directions(A, (b,), p)) == k for b in B))
        assert (bad == min_count(p, k)) == is_net
        if bad == min_count(p, m):
            check_net(left, right, good, p)
        if k == p:
            assert (bad == min_count(p, k)) == full_parallel_lines(A, B, p)
    smallest = min(densities)
    assert smallest == min_count(p, k)
    summary = ', '.join(f'{Fraction(n, p*p)}: {densities[n]}' for n in sorted(densities))
    print(f'p={p} k={k} | packets {len(packets)} | pairs {sum(densities.values())}'
          f' | discrepancy density frequencies {{ {summary} }}')


def mass_beyond_small_packets():
    p, k = 3, 4
    points = tuple(product(range(p), repeat=2))
    packets = list(combinations_with_replacement(points, k))
    vectors = projective_vectors(p)
    profiles = [tuple(projection(A, v, p) for v in vectors) for A in packets]
    equal = 0
    first_gap = 0
    pairs = 0
    for i, j in combinations(range(len(packets)), 2):
        bad = (p - 1) * sum(a != b for a, b in zip(profiles[i], profiles[j]))
        left, right = cancel(packets[i], packets[j])
        equal += check_mass(bad, left, right, p)
        first_gap += 3 * bad * len(left) == 4 * p * (p - 1)
        pairs += 1
    print(f'Mass bound and 4/3 gap at p={p} k={k}: {pairs} unordered pairs,'
          f' {equal} extremal after cancellation, {first_gap} at 4/3.')


def split_packets(p, k):
    H = [a for a in range(1, p) if pow(a, k, p) == 1]
    assert len(H) == k
    return [(a, 0) for a in H], [(0, a) for a in H]


def norm_one_packets(p, k):
    squares = {a*a % p for a in range(p)}
    d = next(a for a in range(1, p) if a not in squares)
    circle = {(a, b) for a in range(p) for b in range(p) if (a*a - d*b*b) % p == 1}

    def multiply(z, w):
        x, y = z
        u, v = w
        return ((x*u + d*y*v) % p, (x*v + y*u) % p)

    def orbit(generator):
        points = [(1, 0)]
        value = generator
        while value != (1, 0):
            points.append(value)
            value = multiply(value, generator)
        return points

    assert len(circle) == p + 1
    powers = next(seq for z in sorted(circle) if len(seq := orbit(z)) == p + 1)
    stride = (p + 1) // k
    assert stride >= 2 and k * stride == p + 1
    return powers[::stride], powers[1::stride]


def parallel_packets(p):
    return [(t, 0) for t in range(p)], [(t, 1) for t in range(p)]


def test_construction(name, p, A, B):
    k = len(A)
    good = good_directions(A, B, p)
    check_net(A, B, good, p)
    # Check actual values on all p^2 evaluations, independently of the formula via projective rays.
    bad = sum(projection(A, v, p) != projection(B, v, p) for v in product(range(p), repeat=2))
    assert bad == min_count(p, k), (name, p, k, bad)
    check_mass(bad, A, B, p)
    return bad


def constructions():
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    counts = Counter()
    for p in primes:
        for k in range(1, p):
            if (p - 1) % k == 0:
                test_construction('axes', p, *split_packets(p, k))
                counts['axes'] += 1
            if (p + 1) % k == 0:
                test_construction('norm-one', p, *norm_one_packets(p, k))
                counts['norm-one'] += 1
        test_construction('parallel', p, *parallel_packets(p))
        counts['parallel'] += 1
    print(f'Constructions verified on all evaluation vectors, primes {primes}')
    print(', '.join(f'{name}: {count}' for name, count in counts.items()))
    for p, k in [(7, 5), (13, 5)]:
        m = k - 1
        if (p - 1) % m == 0:
            A, B = split_packets(p, m)
        else:
            A, B = norm_one_packets(p, m)
        A, B = A + [(0, 0)], B + [(0, 0)]
        bad = (p - 1) * (p + 1 - len(good_directions(A, B, p)))
        assert (p - 1) % k and (p + 1) % k and bad == min_count(p, k - 1)
        print(f'Padded rank-two example p={p} k={k} | discrepancy {Fraction(bad, p*p)}')


if __name__ == '__main__':
    for size in (1, 2, 3):
        exhaustive(3, size)
    exhaustive(5, 2)
    mass_beyond_small_packets()
    constructions()
    print('All assertions passed.')
