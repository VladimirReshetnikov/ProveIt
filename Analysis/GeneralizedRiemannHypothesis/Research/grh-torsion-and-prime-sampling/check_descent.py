"""Exhaust the small cyclotomic orbit products in the fixed-field theorem.

Runs with the Python standard library. Scores are exact integer multiples
of 1/phi(p**h). None denotes an infinite score at a marked torsion point.
Every multiset of primitive-root orbits of total orbit count L<=phi(p**s)
is tested. This checks the full finite minimax profile for those products.
The proof in the paper also covers roots which are not torsion points.
"""

from itertools import combinations_with_replacement
from math import comb


def cyclotomic_orbits(p, s, h):
    """Galois orbits from multiplication, given compatible primitive roots."""
    modulus = p**h
    units = [a for a in range(1, modulus) if a % p]
    group = [u for u in units if u % (p**s) == 1]
    remaining = set(units)
    orbits = []
    while remaining:
        first = min(remaining)
        orbit = sorted({first * u % modulus for u in group})
        orbits.append(orbit)
        remaining.difference_update(orbit)
    return units, orbits


def orbit_loss(a, orbit, p):
    """Sum the leaf distances after subtracting one radial valuation per root."""
    if a in orbit:
        return None
    score = 0
    for b in orbit:
        difference = abs(a - b)
        power = 1
        while difference % p == 0:
            difference //= p
            power *= p
        score += power - 1
    return score


def least_score(counts, rows):
    """Minimum over test points; a minimum over entirely marked points is infinite."""
    minimum = None
    for row in rows:
        if any(count and weight is None for count, weight in zip(counts, row)):
            continue
        total = sum(count * weight for count, weight in zip(counts, row) if count)
        if minimum is None or total < minimum:
            minimum = total
    return minimum


def check(p, s, h):
    units, orbits = cyclotomic_orbits(p, s, h)
    radial_denominator = len(units)
    base_denominator = (p - 1) * p ** (s - 1)
    assert len(orbits) == base_denominator
    assert all(len(orbit) * base_denominator == radial_denominator for orbit in orbits)
    rows = [[orbit_loss(a, orbit, p) for orbit in orbits] for a in units]
    expected_denominators = [(p - 1) * p ** (j - 1) for j in range(1, s)]
    profiles = []
    total_packets = 0
    for size in range(base_denominator + 1):
        best = -1
        packet_count = 0
        for selection in combinations_with_replacement(range(len(orbits)), size):
            counts = [0] * len(orbits)
            for selected_orbit in selection:
                counts[selected_orbit] += 1
            score = least_score(counts, rows)
            packet_count += 1
            if score is None:
                best = None
            elif best is not None:
                best = max(score, best)
        assert packet_count == comb(len(orbits) + size - 1, size)
        total_packets += packet_count
        expected = None
        if size < base_denominator:
            base_score = sum(den * (size // den) for den in expected_denominators)
            expected = (radial_denominator // base_denominator) * base_score
        if best != expected:
            raise AssertionError((p, s, h, size, best, expected))
        profiles.append("inf" if best is None else str(best))
    print(f"p={p}, s={s}, h={h}, packets={total_packets}, "
          f"phi(p^h)*maximin=[{', '.join(profiles)}]")
    return total_packets


def main():
    cases = [(2, 1, 3), (2, 2, 4), (2, 3, 5), (2, 4, 5),
             (3, 1, 3), (3, 2, 3), (5, 1, 2), (7, 1, 2)]
    total = sum(check(p, s, h) for p, s, h in cases)
    print(f"Verified {len(cases)} field/shell cases and {total} orbit multisets.")


if __name__ == "__main__":
    main()
