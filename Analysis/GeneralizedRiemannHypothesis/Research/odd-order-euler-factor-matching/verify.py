#!/usr/bin/env python3
"""Run exact finite checks for the packet matching bounds, using only Python."""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb, isqrt, prod


def dot(x, y, p):
    return sum(a * b for a, b in zip(x, y)) % p


def directions(p, rank):
    """Use the representative whose first nonzero coordinate equals one."""
    return [v for v in product(range(p), repeat=rank)
            if next((c for c in v if c), 0) == 1]


def proven_bound(p, rank, k):
    leading_power = 1
    while leading_power * p <= k:
        leading_power *= p
    if leading_power >= p ** (rank - 1):
        return Fraction(p - 1, p ** rank)
    digit = k // leading_power
    return Fraction((p - 1) * (p + 1 - digit), leading_power * p * p)


def packet_signatures(p, rank, k, rays, points=None):
    """Pack the exact multisets of residues along the projective directions."""
    if points is None:
        points = list(product(range(p), repeat=rank))
    codes = {x: i for i, x in enumerate(combinations_with_replacement(range(p), k))}
    # Leave one guard bit per field for the pairwise comparison below.
    width = max(1, (len(codes) - 1).bit_length()) + 1
    projections = [[dot(x, v, p) for x in points] for v in rays]
    signatures = []
    for packet in combinations_with_replacement(range(len(points)), k):
        key = 0
        for i, values in enumerate(projections):
            local = tuple(sorted(values[x] for x in packet))
            key |= codes[local] << (i * width)
        signatures.append(key)
    return width, signatures


def agreement_distribution(rays_count, width, signatures):
    """Count all unordered pairs by the number of agreement directions.

    For each subset S of directions, grouping on the S-projection counts the
    pairs agreeing everywhere on S. If N_j pairs agree on j directions, the
    sum of the group counts for |S|=i equals sum_j binom(j,i) N_j.
    """
    blocks = [((1 << width) - 1) << (i * width) for i in range(rays_count)]
    masks = [0]
    for block in blocks:
        masks.extend(mask | block for mask in masks[:])
    moments = [0] * (rays_count + 1)
    for subset, mask in enumerate(masks):
        buckets = Counter(signature & mask for signature in signatures)
        pairs = sum(n * (n - 1) // 2 for n in buckets.values())
        moments[subset.bit_count()] += pairs
    counts = moments.copy()
    for i in reversed(range(rays_count + 1)):
        counts[i] -= sum(comb(j, i) * counts[j] for j in range(i + 1, rays_count + 1))
    assert all(count >= 0 for count in counts)
    assert sum(counts) == comb(len(signatures), 2)
    return counts


def exhaustive_check(p, rank, k):
    rays = directions(p, rank)
    width, signatures = packet_signatures(p, rank, k, rays)
    distinct = len(set(signatures))
    assert distinct == len(signatures)
    agreement = agreement_distribution(len(rays), width, signatures)
    exact = {(len(rays) - j): n for j, n in enumerate(agreement) if n}
    minimum = min(exact)
    density = Fraction((p - 1) * minimum, p ** rank)
    assert density == proven_bound(p, rank, k)
    return {
        "p": p, "rank": rank, "size": k, "projective_directions": len(rays),
        "packets": len(signatures), "distinct_full_signatures": distinct,
        "unordered_distinct_pairs": sum(exact.values()),
        "pair_counts_by_disagreement_directions": dict(sorted(exact.items())),
        "minimum_disagreement_density": str(density),
    }


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for n in range(2, isqrt(limit) + 1):
        if sieve[n]:
            sieve[n * n::n] = bytes((limit - n * n) // n + 1)
    return [n for n, prime in enumerate(sieve) if prime]


def least_primitive_root_and_logs(q, order):
    for g in range(2, q):
        powers = [pow(g, i, q) for i in range(q - 1)]
        if len(set(powers)) == q - 1:
            return g, {u: i % order for i, u in enumerate(powers)}
    raise AssertionError(f"No primitive root found modulo {q}")


def arithmetic_example():
    p = 5
    factors = [11, 31, 41]
    modulus = prod(factors)
    roots, logs = zip(*(least_primitive_root_and_logs(q, p) for q in factors))
    base = [(1, 0), (2, 2), (2, 3)]
    packet_a = [(i, j, t) for i, j in base for t in range(p)]
    packet_c = [tuple(-x % p for x in point) for point in packet_a]

    def histogram(packet, v):
        return tuple(sorted(dot(point, v, p) for point in packet))

    pairs = {v: (histogram(packet_a, v), histogram(packet_c, v))
             for v in product(range(p), repeat=3)}
    bad = {v for v, (left, right) in pairs.items() if left != right}
    density = Fraction(len(bad), len(pairs))
    assert density == proven_bound(p, 3, 15) == Fraction(12, 125)

    def coordinates(n):
        return tuple(table[n % q] for table, q in zip(logs, factors))

    unit_classes = [u for u in range(modulus) if all(u % q for q in factors)]
    class_counts = Counter(coordinates(u) for u in unit_classes)
    assert len(class_counts) == len(pairs)
    assert len(set(class_counts.values())) == 1
    bad_classes = sum(class_counts[v] for v in bad)
    limit = 100_000
    good_primes = [q for q in primes_up_to(limit) if q not in factors]
    witnesses = [q for q in good_primes if coordinates(q) in bad]
    return {
        "character_order": p, "rank": 3, "packet_size": len(packet_a),
        "modulus": modulus, "prime_factors": factors, "least_primitive_roots": roots,
        "base_packet": base, "disagreement_vectors": sorted(bad),
        "number_of_evaluation_vectors": len(pairs),
        "unit_residue_classes": len(unit_classes), "unit_classes_per_vector": next(iter(class_counts.values())),
        "disagreeing_unit_classes": bad_classes, "density": str(density),
        "first_ten_distinguishing_primes": witnesses[:10],
        "prime_range_upper_limit": limit, "unramified_primes_in_range": len(good_primes),
        "distinguishing_primes_in_range": len(witnesses),
    }


def primitive_coefficients(p, rank):
    signs = [(eps, prod(eps)) for eps in product((-1, 1), repeat=rank - 1)]
    coefficients = {}
    for x in product(range(p), repeat=rank):
        value = 0
        for eps, weight in signs:
            level = (x[0] + sum(sign * a for sign, a in zip(eps, x[1:]))) % p
            if rank % 2 == 0:
                value += weight * (level == 0)
            else:
                value += weight * ((level == 1) - (level == p - 1))
        if value:
            assert all(x)
            coefficients[x] = value
    assert coefficients and sum(coefficients.values()) == 0
    return coefficients


def primitive_witness_check(p, rank):
    coefficients = primitive_coefficients(p, rank)
    size = sum(n for n in coefficients.values() if n > 0)
    size_bound = (2 * p) ** (rank - 1)
    assert 0 < size <= size_bound
    support_size = 0
    for v in product(range(p), repeat=rank):
        histogram = [0] * p
        for x, count in coefficients.items():
            histogram[dot(v, x, p)] += count
        t = v[0]
        support_condition = t != 0 and all(a in (t, p - t) for a in v[1:])
        assert any(histogram) == support_condition
        support_size += support_condition
        # Subtract the cyclotomic coefficient vector of p^(r-1) J(v).
        # Zero at zeta_p is equivalent to all resulting coefficients equal.
        if support_condition:
            amplitude = (-1) ** v[1:].count(p - t) * p ** (rank - 1)
            if rank % 2 == 0:
                histogram[0] -= amplitude
            else:
                histogram[t] -= amplitude
                histogram[p - t] += amplitude
        assert len(set(histogram)) == 1
    assert support_size == (p - 1) * 2 ** (rank - 1)
    return {
        "p": p, "rank": rank, "integral_nonzero_coefficients": len(coefficients),
        "positive_mass": size, "negative_mass": size, "proven_upper_bound_for_each_mass": size_bound,
        "evaluation_vectors_checked": p ** rank, "disagreeing_vectors": support_size,
        "disagreement_density": str(Fraction(support_size, p ** rank)),
    }


def primitive_cubic_exhaustive(rank, k):
    p = 3
    points = list(product((1, 2), repeat=rank))
    rays = directions(p, rank)
    width, signatures = packet_signatures(p, rank, k, rays, points)
    assert len(signatures) == len(set(signatures))
    # The XOR of two signature fields is nonzero precisely at a mismatch.
    # Adding a field filled with all ones except its guard bit sets the
    # guard if and only if that field's XOR is nonzero, without carry out.
    offsets = [i * width for i in range(len(rays))]
    lower_ones = sum(((1 << (width - 1)) - 1) << off for off in offsets)
    guards = sum(1 << (off + width - 1) for off in offsets)
    histogram = Counter(((((x ^ y) + lower_ones) & guards).bit_count())
                        for x, y in combinations(signatures, 2))
    assert sum(histogram.values()) == comb(len(signatures), 2) and histogram[0] == 0
    minimum = Fraction(2 * min(histogram), 3 ** rank)
    dimensions = min(rank, (2 * k).bit_length() - 1)
    assert minimum == Fraction(2, 3) ** dimensions
    return {
        "p": p, "rank": rank, "size": k, "primitive_characters": len(points),
        "packets": len(signatures), "unordered_distinct_pairs": sum(histogram.values()),
        "pair_counts_by_disagreement_directions": dict(sorted(histogram.items())),
        "minimum_disagreement_density": str(minimum),
    }


def five_factor_septimic_example():
    p = 7
    factors = (29, 43)
    packet_a = [(4, 3), (2, 3), (3, 4), (3, 2), (3, 3)]
    packet_c = [(5, 5), (1, 5), (5, 1), (1, 1), (3, 3)]
    assert all(all(x) for x in packet_a + packet_c)
    bad = {v for v in product(range(p), repeat=2)
           if sorted(dot(v, x, p) for x in packet_a) != sorted(dot(v, x, p) for x in packet_c)}
    assert len(bad) == 24
    roots, log_tables = zip(*(least_primitive_root_and_logs(q, p) for q in factors))

    def coordinates(n):
        return tuple(table[n % q] for table, q in zip(log_tables, factors))

    units = [u for u in range(prod(factors)) if all(u % q for q in factors)]
    bad_class_count = sum(coordinates(u) in bad for u in units)
    assert Fraction(bad_class_count, len(units)) == Fraction(24, 49)
    primes = [q for q in primes_up_to(100_000) if q not in factors]
    witnesses = [q for q in primes if coordinates(q) in bad]
    return {
        "p": p, "rank": 2, "packet_size": 5, "prime_factors": factors,
        "modulus": prod(factors), "least_primitive_roots": roots,
        "packet_a": packet_a, "packet_c": packet_c,
        "disagreement_density": "24/49", "agreement_density": "25/49",
        "disagreeing_unit_classes": bad_class_count, "unit_residue_classes": len(units),
        "first_ten_distinguishing_primes": witnesses[:10],
        "prime_range_upper_limit": 100_000, "unramified_primes_in_range": len(primes),
        "distinguishing_primes_in_range": len(witnesses),
    }


def main():
    parameters = [(3, 2, k) for k in range(1, 5)]
    parameters += [(3, 3, k) for k in (2, 3)]
    parameters += [(5, 2, k) for k in range(1, 5)]
    data = {
        "exhaustive": [exhaustive_check(*case) for case in parameters],
        "arithmetic_example": arithmetic_example(),
        "primitive_witnesses": [primitive_witness_check(p, rank)
                                for p in (3, 5, 7) for rank in range(1, 5)],
        "five_factor_septimic_example": five_factor_septimic_example(),
        "exhaustive_primitive_cubic": [primitive_cubic_exhaustive(rank, k)
                                       for rank in (3, 4) for k in range(1, 5)],
    }
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
