#!/usr/bin/env python3
"""Exact finite checks for power-map layers of weighted prime zeta functions.

Run with Python 3.8 or later, using its standard library. No zero ordinates
or floating-point calculations enter these checks.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, prod


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def factor(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        factors[n] = 1
    return factors


def moebius(n):
    factors = factor(n)
    return 0 if any(a > 1 for a in factors.values()) else (-1) ** len(factors)


def units(q):
    return [a for a in range(1, q) if gcd(a, q) == 1]


def cyclic_orders(q):
    """Cyclic factor orders for the units of Z/qZ by the prime-power formula."""
    for p, e in factor(q).items():
        if p == 2 and e >= 3:
            yield 2
            yield 2 ** (e - 2)
        else:
            yield (p - 1) * p ** (e - 1)


def verify_ranks():
    pairs = 0
    for q in range(2, 71):
        group = units(q)
        orders = list(cyclic_orders(q))
        require(prod(orders) == len(group), (q, "group order"))
        for m in range(1, 121):
            scalar = moebius(m)
            # The row at g of the operator on delta-function coordinates
            # is the coordinate row e_(g^m) times the common scalar.
            # Each distinct nonzero row is an independent pivot over Q.
            pivots = {pow(g, m, q) for g in group} if scalar else set()
            expected = prod(n // gcd(n, m) for n in orders) if scalar else 0
            require(len(pivots) == expected, (q, m, len(pivots), expected))
            pairs += 1
    print(f"Power-map ranks: {pairs} (q,m) pairs agree with the CRT formula"
          " (2 <= q <= 70, 1 <= m <= 120).")


def verify_inversion():
    # In the logarithmic-derivative expansion a local prime with residue g
    # contributes mu(m) f((g^m)^(k/m)) at exponent k for each m dividing k.
    # Directly expand several Euler factors and compare at every degree.
    tests = 0
    for q in (8, 15, 16, 24, 31, 45, 63):
        group = units(q)
        weight = {a: ((a * a + 11 * a + 2) % 13) - 6 for a in group}
        for g in group:
            coefficients = [0] * 73
            for m in range(1, 73):
                gm = pow(g, m, q)
                for ell in range(1, 72 // m + 1):
                    coefficients[m * ell] += moebius(m) * weight[pow(gm, ell, q)]
            require(coefficients[1] == weight[g] and not any(coefficients[2:]),
                    (q, g, "Euler coefficient mismatch"))
            tests += 72
    print(f"Moebius cancellation: {tests} local coefficients agree through"
          " prime-power degree 72.")


PRIMES = (2, 3, 5)


def mask(m):
    return sum(1 << i for i, p in enumerate(PRIMES) if m % p == 0)


def is_subset(small, large):
    return (small & large) == small


def verify_mod31():
    group = units(31)
    powers = [pow(3, e, 31) for e in range(30)]
    require(len(set(powers)) == 30, "3 does not generate the unit group")
    single = {3: 1}
    race = {9: 1, 27: -1}
    print("Modulus 31, generator 3. Rows are squarefree masks, represented by")
    print("their product d. Rank is 30/d. Last columns count nonzero coordinates.")
    print("  d   rank   delta_3   delta_9-delta_27")
    single_masks = set()
    race_masks = set()
    for s in range(8):
        d = prod(p for i, p in enumerate(PRIMES) if s & (1 << i))
        images = [pow(g, d, 31) for g in group]
        single_count = sum(bool(single.get(a)) for a in images)
        race_count = sum(bool(race.get(a)) for a in images)
        require(len(set(images)) == 30 // d, (d, "rank"))
        require(bool(single_count) == (d == 1), (d, "single"))
        require(bool(race_count) == (d in (1, 2, 3)),
                (d, "race"))
        if single_count:
            single_masks.add(s)
        if race_count:
            race_masks.add(s)
        print(f"{d:3d} {len(set(images)):6d} {single_count:9d} {race_count:18d}")
    for m in range(1, 1001):
        sf = bool(moebius(m))
        for f, allowed in ((single, sf and gcd(m, 30) == 1),
                           (race, sf and m % 5 != 0 and m % 6 != 0)):
            visible = sf and any(f.get(pow(g, m, 31), 0) for g in group)
            require(visible == allowed, (m, f, allowed))

    # Local conditional probabilities given p^2 does not divide m.
    # At primes outside {2,3,5} the squarefreeness factors cancel in the
    # ratio. CRT counting modulo 2^2 3^2 5^2 checks the product exactly.
    period = prod(p * p for p in PRIMES)
    frequencies = Counter(mask(m) for m in range(period)
                          if all(m % (p * p) for p in PRIMES))
    total = sum(frequencies.values())
    for s in range(8):
        theory = prod(Fraction(1 if s & (1 << i) else p, p + 1)
                      for i, p in enumerate(PRIMES))
        require(Fraction(frequencies[s], total) == theory, (s, "mask density"))
    for name, masks, expected in (("delta_3", single_masks, Fraction(5, 12)),
                                  ("delta_9-delta_27", race_masks, Fraction(55, 72))):
        count = sum(frequencies[s] for s in masks)
        density = Fraction(count, total)
        require(density == expected, (name, density))
        print(f"{name} relative density among squarefree indices: "
              f"{count}/{total} = {density}.")
    return powers


def verify_downsets(powers):
    # Realize all eight intrinsic signatures by actual residues. The
    # signature of a is exactly the set of p for which a is a pth power.
    representative = {}
    group = units(31)
    for a in powers:
        sig = sum(1 << i for i, p in enumerate(PRIMES)
                  if a in {pow(g, p, 31) for g in group})
        representative.setdefault(sig, a)
    require(len(representative) == 8, "missing signature")
    image_by_mask = []
    for s in range(8):
        d = prod(p for i, p in enumerate(PRIMES) if s & (1 << i))
        image_by_mask.append({pow(g, d, 31) for g in group})
    min_support = {}
    for size in range(9):
        for signatures in combinations(range(8), size):
            support = {representative[t] for t in signatures}
            visible = frozenset(s for s, image in enumerate(image_by_mask)
                                if support & image)
            min_support.setdefault(visible, size)
    lattice_ideals = set()
    for bits in range(256):
        family = frozenset(s for s in range(8) if bits & (1 << s))
        if all(t in family for s in family for t in range(8) if is_subset(t, s)):
            lattice_ideals.add(family)
    require(lattice_ideals == set(min_support), "unrealizable or extraneous family")
    histogram = Counter()
    for family, best in min_support.items():
        maxima = {s for s in family if not any(s != t and is_subset(s, t)
                                                for t in family)}
        require(best == len(maxima), (family, best, maxima))
        histogram[best] += 1
    print(f"Downsets: {len(lattice_ideals)} of 256 families are downsets;"
          " all realized. All 256 signature supports checked.")
    print("Number of downsets by minimum support cardinality: " +
          ", ".join(f"{k} -> {histogram[k]}" for k in sorted(histogram)) + ".")


if __name__ == "__main__":
    verify_ranks()
    verify_inversion()
    verify_downsets(verify_mod31())
    print("All exact checks passed.")
