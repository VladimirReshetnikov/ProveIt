#!/usr/bin/env python3
"""Exact finite checks for two packets of six primitive quartic characters.

Run with Python 3.10 or later. Every count uses integers. The analytic
limits for zero ordinates are treated separately in the accompanying paper.
"""

from itertools import combinations
from math import comb, prod


DIMENSION = 4
GROUP_SIZE = 1 << DIMENSION
GROUP = range(GROUP_SIZE)
CONDUCTOR_PRIMES = (5, 13, 17, 29)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def bit(point, index):
    return (point >> index) & 1


def support_mask(points):
    return sum(1 << point for point in points)


def translated_mask(points, shift):
    return support_mask(point ^ shift for point in points)


def first_quadratic(point):
    return (bit(point, 0) * bit(point, 1)) ^ (bit(point, 2) * bit(point, 3))


def second_quadratic(point):
    return first_quadratic(point) ^ (bit(point, 0) * bit(point, 2))


def walsh_sum(points, frequency):
    return sum((-1) ** ((point & frequency).bit_count() % 2) for point in points)


def difference_counts(points):
    counts = [0] * GROUP_SIZE
    for left in points:
        for right in points:
            counts[left ^ right] += 1
    return counts


def enumerate_difference_sets():
    target = [6] + [2] * (GROUP_SIZE - 1)
    supports = set()
    orbits = set()
    for points in combinations(GROUP, 6):
        if difference_counts(points) == target:
            supports.add(support_mask(points))
            orbit = {translated_mask(points, shift) for shift in GROUP}
            check(len(orbit) == GROUP_SIZE, "nontrivial translation stabilizer")
            orbits.add(min(orbit))
    check(len(supports) == 448, "difference-set count")
    check(len(orbits) == 28, "translation-orbit count")
    return supports, orbits


def enumerate_quadratic_forms():
    """Construct every alternating form by its six upper-triangular bits."""
    pairs = list(combinations(range(DIMENSION), 2))
    all_masks = set()
    orbit_representatives = set()
    nonsingular = 0
    for coefficients in range(1 << len(pairs)):
        terms = [pair for number, pair in enumerate(pairs) if bit(coefficients, number)]
        values = [sum(bit(x, i) * bit(x, j) for i, j in terms) % 2 for x in GROUP]
        radical = [
            x for x in GROUP if all((values[x ^ y] ^ values[x] ^ values[y]) == 0
                                    for y in GROUP)
        ]
        if len(radical) > 1:
            continue
        nonsingular += 1
        # The smaller of the two level sets has size six for a nonsingular form.
        level = 1 if sum(values) < GROUP_SIZE // 2 else 0
        points = [x for x in GROUP if values[x] == level]
        check(len(points) == 6, "quadratic level-set size")
        orbit = {translated_mask(points, shift) for shift in GROUP}
        all_masks.update(orbit)
        orbit_representatives.add(min(orbit))
    check(nonsingular == 28, "nonsingular alternating-form count")
    return all_masks, orbit_representatives


def local_quartic_table(prime):
    """Encode the character value i^k by k mod 4 on the local unit group."""
    for generator in range(2, prime):
        powers = [pow(generator, exponent, prime) for exponent in range(prime - 1)]
        if len(set(powers)) == prime - 1:
            return {value: exponent % 4 for exponent, value in enumerate(powers)}
    raise ValueError(f"missing primitive root modulo {prime}")


def gaussian_trace(points, local_phases):
    # At coordinate i, a packet member has quartic exponent 1+2*x_i.
    powers = [0] * 4
    for point in points:
        phase = sum((1 + 2 * bit(point, i)) * local
                    for i, local in enumerate(local_phases)) % 4
        powers[phase] += 1
    return powers[0] - powers[2], powers[1] - powers[3]


def check_prime_residues(a, b):
    modulus = prod(CONDUCTOR_PRIMES)
    tables = [local_quartic_table(prime) for prime in CONDUCTOR_PRIMES]
    counts = [0] * GROUP_SIZE
    differing = 0
    at_two = None
    for residue in range(1, modulus):
        if any(residue % prime == 0 for prime in CONDUCTOR_PRIMES):
            continue
        phases = [table[residue % prime] for prime, table in zip(CONDUCTOR_PRIMES, tables)]
        frequency = sum((phase % 2) << i for i, phase in enumerate(phases))
        counts[frequency] += 1
        first, second = gaussian_trace(a, phases), gaussian_trace(b, phases)
        discrepancy = (first[0] - second[0], first[1] - second[1])
        square = sum(c * c for c in discrepancy)
        predicted = bit(frequency, 1) * bit(frequency, 3)
        check(square == 16 * predicted, "prime trace or quadratic dual identity")
        differing += bool(square)
        if residue == 2:
            at_two = frequency, first, second, square
    units = sum(counts)
    check(len(set(counts)) == 1 and units == 21504, "CRT fibers")
    check(4 * differing == units, "prime residue-class mismatch fraction")
    check(at_two is not None and at_two[3] == 16, "gap at the prime two")
    return modulus, units, differing, at_two


def main():
    all_supports, orbit_representatives = enumerate_difference_sets()
    quadratic_supports, quadratic_representatives = enumerate_quadratic_forms()
    check(quadratic_supports == all_supports, "quadratic construction misses a support")
    check(quadratic_representatives == orbit_representatives, "quadratic orbit mismatch")

    a = [x for x in GROUP if first_quadratic(x)]
    b = [x for x in GROUP if second_quadratic(x)]
    check(all(support_mask(a) != translated_mask(b, t) for t in GROUP),
          "example packets are translates")
    spectrum_a = [walsh_sum(a, v) for v in GROUP]
    spectrum_b = [walsh_sum(b, v) for v in GROUP]
    check([s * s for s in spectrum_a] == [s * s for s in spectrum_b] == [36] + [4] * 15,
          "pair spectra")
    mismatch_counts = []
    for shift in GROUP:
        spectrum_twist = [walsh_sum([x ^ shift for x in b], v) for v in GROUP]
        mismatch_counts.append(sum(x != y for x, y in zip(spectrum_a, spectrum_twist)))
    check(set(mismatch_counts) == {4, 8, 12}, "twisted mismatch fractions")
    modulus, units, differing, at_two = check_prime_residues(a, b)
    frequency, first, second, squared_gap = at_two
    print(f"Six-point supports tested: {comb(16, 6)}")
    print(f"(16,6,2) difference sets: {len(all_supports)}")
    print(f"Translation orbits: {len(orbit_representatives)} (each of size 16)")
    print("Independent alternating-form construction recovers every support and orbit.")
    print(f"A (x1 is the least significant bit): {a}")
    print(f"B (same convention): {b}")
    print("Both Walsh power spectra: 36 at zero, 4 at each nonzero frequency.")
    print("Mismatch counts out of 16 frequencies under the 16 twists:",
          {k: mismatch_counts.count(k) for k in sorted(set(mismatch_counts))})
    print(f"Conductor: {modulus}. Unit classes: {units}. Untwisted mismatches: {differing} (1/4).")
    print(f"Prime 2: evaluation coordinates {tuple(bit(frequency, i) for i in range(4))}.")
    print(f"Packet traces at 2 as Gaussian integer pairs: A={first}, B={second}.")
    print(f"Squared trace gap at 2: {squared_gap}. Absolute trace gap: 4.")
    print("All exact finite checks passed.")


if __name__ == "__main__":
    main()
