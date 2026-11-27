#!/usr/bin/env python3
"""Exact finite checks for principal-kernel witnesses over the two-element field.

Run with Python 3.10 or later. Only the standard library is used.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import factorial


def insert_basis(basis, vector):
    """Insert a binary row into a canonical reduced basis, represented as integers."""
    for row in basis:
        if (vector >> (row.bit_length() - 1)) & 1:
            vector ^= row
    if not vector:
        return basis
    pivot = 1 << (vector.bit_length() - 1)
    reduced = (row ^ vector if row & pivot else row for row in basis)
    return tuple(sorted((*reduced, vector), reverse=True))


def principal_nullity(columns, mask):
    basis = []
    active = mask
    while active:
        bit = active & -active
        vector = columns[bit.bit_length() - 1] & mask
        while vector:
            pivot = vector.bit_length() - 1
            if pivot >= len(basis):
                basis.extend([0] * (pivot + 1 - len(basis)))
            if not basis[pivot]:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
        active ^= bit
    return mask.bit_count() - sum(bool(row) for row in basis)


def orthonormal_bases(n):
    # Distinct mutually orthogonal unit vectors are automatically independent.
    odd = tuple(v for v in range(1 << n) if v.bit_count() % 2)

    def complete(chosen, candidates):
        if len(chosen) == n:
            yield chosen
            return
        for column in candidates:
            compatible = tuple(v for v in candidates if (v & column).bit_count() % 2 == 0)
            yield from complete((*chosen, column), compatible)

    yield from complete((), odd)


def orthogonal_check():
    print("Maximum principal nullity and complement identity for every orthogonal matrix")
    orders = (1, 2, 6, 48, 720, 23040)
    group_orders = (1,) + orders
    maxima = {}
    for n, expected in enumerate(orders, 1):
        all_coordinates = (1 << n) - 1
        histogram = Counter()
        m = n // 2
        fixed_support = (1 << m) - 1
        saturated = 0
        for columns in orthonormal_bases(n):
            nullities = [principal_nullity(columns, mask) for mask in range(1 << n)]
            assert all(value == nullities[all_coordinates ^ mask] for mask, value in enumerate(nullities))
            histogram[max(nullities)] += 1
            saturated += nullities[fixed_support] == m
        assert sum(histogram.values()) == expected
        maxima[n] = histogram[m]
        predicted = group_orders[n - m] ** 2
        assert saturated == predicted
        print(f"  n={n} group_order={expected} histogram={dict(sorted(histogram.items()))}"
              f" saturated_fixed_support={saturated}/{expected}")
    return maxima


def orthogonal_order(d):
    # Product formula for the binary dot-product isometry group, including d=0.
    order = Fraction(2 ** (d * (d - 1) // 2))
    for j in range(1, (d - 1) // 2 + 1):
        order *= 1 - Fraction(1, 4 ** j)
    assert order.denominator == 1
    return order.numerator


def even_endpoint_check(exhaustive):
    print("Even saturated counts from the exponential generating series")
    coefficients = [Fraction(1)]
    for m in range(1, 7):
        square_coefficient = Fraction(orthogonal_order(m), factorial(m)) ** 2
        internal = sum(coefficients[i] * coefficients[m - i] for i in range(1, m))
        coefficients.append((square_coefficient - internal) / 2)
        saturated = factorial(2 * m) * coefficients[m]
        assert saturated.denominator == 1
        if 2 * m in exhaustive:
            assert saturated == exhaustive[2 * m]
        assert 0 < saturated <= orthogonal_order(2 * m)
        print(f"  n={2 * m} saturated_matrices={saturated.numerator}"
              f" group_order={orthogonal_order(2 * m)}")


def row_gram(row, d):
    return sum(((row >> i) & (row >> j) & 1) << pos
               for pos, (i, j) in enumerate(combinations_with_diagonal(d)))


def combinations_with_diagonal(d):
    return [(i, j) for i in range(d) for j in range(i, d)]


def gram_check():
    print("Exact arbitrary-Gram completion counts for independent augmented columns")
    count = 0
    for d in (1, 2, 3):
        # Each bottom row is (1, z); full rank tests independence of (c,z_1,...,z_d).
        choices = [(1 << d | z, row_gram(z, d)) for z in range(1 << d)]
        states = {(0, ()): 1}
        for b in range(1, 2 * d + 5):
            next_states = defaultdict(int)
            for (old_gram, basis), mass in states.items():
                for augmented, update in choices:
                    key = old_gram ^ update, insert_basis(basis, augmented)
                    next_states[key] += mass
            states = next_states
            assert sum(states.values()) == 2 ** (b * d)
            if b < 2 * d + 2:
                continue
            h = b * d - d * (d + 1) // 2
            baseline = 1 << h
            loss = sum(Fraction(2 ** (2 * i + 2), 2 ** b) for i in range(d))
            total = Counter()
            good = Counter()
            for (gram, basis), mass in states.items():
                total[gram] += mass
                if len(basis) == d + 1:
                    good[gram] += mass
            for gram in range(1 << (d * (d + 1) // 2)):
                assert baseline * (1 - loss) <= good[gram] <= baseline
                assert good[gram] <= total[gram] <= baseline * (1 + Fraction(2 ** (2 * d + 2), 2 ** b))
                count += 1
            print(f"  d={d} b={b} target_grams={len(total)} baseline={baseline}"
                  f" admissible_range={min(good.values())}..{max(good.values())}"
                  f" all_range={min(total.values())}..{max(total.values())}")
    print(f"  Gram targets checked: {count}")


def collision_check():
    print("Gram collision identity for independent binary frames")
    for d in (1, 2, 3, 4):
        rows = Counter(row_gram(row, d) for row in range(1 << d))
        law = Counter({0: 1})
        snapshots = {}
        for b in range(1, 2 * d + 5):
            next_law = Counter()
            for g, multiplicity in law.items():
                for update, weight in rows.items():
                    next_law[g ^ update] += multiplicity * weight
            law = next_law
            snapshots[b] = law
            if b % 2 == 0:
                half = snapshots[b // 2]
                collisions = sum(count * count for count in half.values())
                assert law[0] == collisions
        print(f"  d={d}: stacked-frame zero Gram counts matched for"
              f" {d + 2} row-pair dimensions")


def subspaces(mask, rank):
    vectors = [v for v in range(mask + 1) if v & mask == v]
    spaces = set()
    for generators in combinations(vectors[1:], rank):
        span = {0}
        for v in generators:
            span |= {x ^ v for x in span}
        if len(span) == 1 << rank:
            spaces.add(frozenset(span))
    return spaces


def verify_quotient_formula(n, relation, planes):
    """Check intersections of one linear relation against every coordinate-split dimension."""
    mask = (1 << n) - 1
    pairs = [(v & mask, v >> n) for v in relation]
    w = {x for x, y in pairs if y == 0}
    w_prime = {y for x, y in pairs if x == 0}
    if len(w) != len(w_prime):
        return 0
    u = {x for x, _ in pairs}
    u_prime = {y for _, y in pairs}
    # Representatives chosen by the numeric minimum in each coset.
    coset = {x: min(x ^ h for h in w) for x in u}
    coset_prime = {y: min(y ^ h for h in w_prime) for y in u_prime}
    residual_map = {coset[x]: coset_prime[y] for x, y in pairs}
    assert all(residual_map[coset[x]] == coset_prime[y] for x, y in pairs)
    assert len(residual_map) == len(set(residual_map.values()))
    checks = 0
    for e in range(n + 1):
        for p in planes[n - e]:
            a_size = len(p & w)
            left_image = {residual_map[coset[x]] for x in p & u}
            for p_prime in planes[e]:
                a_prime_size = len(p_prime & w_prime)
                right_image = {coset_prime[y] for y in p_prime & u_prime}
                actual = sum(x in p and y in p_prime for x, y in pairs)
                predicted = a_size * a_prime_size * len(left_image & right_image)
                assert actual == predicted
                assert actual <= a_size * len(p_prime & u_prime)
                checks += 1
    return checks


def relation_check():
    print("Linear-relation intersection formula over all independent test-plane pairs")
    for n in (1, 2, 3, 4):
        mask = (1 << n) - 1
        planes = {d: subspaces(mask, d) for d in range(n + 1)}
        if n <= 3:
            relations = subspaces((1 << (2 * n)) - 1, n)
            description = "all n-planes with equal axis intersections"
        else:
            # Canonical representative of each double-GL orbit with equal axis dimensions.
            relations = []
            for r in range(n // 2 + 1):
                basis = ([1 << i for i in range(r)]
                         + [1 << (n + i) for i in range(r)]
                         + [(1 << i) | (1 << (n + i)) for i in range(r, n - r)])
                span = {0}
                for vector in basis:
                    span |= {x ^ vector for x in span}
                relations.append(frozenset(span))
            description = "one representative for each equal-axis orbit"
        nonempty = 0
        checks = 0
        for relation in relations:
            total = verify_quotient_formula(n, relation, planes)
            nonempty += bool(total)
            checks += total
        print(f"  n={n}: {description}, relations={nonempty}, plane_pairs={checks}")


if __name__ == "__main__":
    histogram_maxima = orthogonal_check()
    even_endpoint_check(histogram_maxima)
    gram_check()
    collision_check()
    relation_check()
    print("All exact checks passed.")
