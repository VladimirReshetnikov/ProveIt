"""Exact small finite-cover checks for torsion.tex (Python standard library)."""
from fractions import Fraction
from itertools import combinations, product
from math import gcd


def unit_group(modulus):
    return [a for a in range(1, modulus) if gcd(a, modulus) == 1]


def order(a, modulus):
    value = a % modulus
    length = 1
    while value != 1:
        value = value * a % modulus
        length += 1
    return length


def minimum_cover(units, multipliers, modulus):
    """Exhaust all subsets by increasing size. Each mask records covered starts."""
    goal = (1 << len(units)) - 1
    masks = []
    for marked in units:
        starts = {marked * pow(j, -1, modulus) % modulus for j in multipliers}
        masks.append(sum(1 << i for i, a in enumerate(units) if a in starts))
    for size in range(1, len(units) + 1):
        for choice in combinations(masks, size):
            bits = 0
            for mask in choice:
                bits |= mask
            if bits == goal:
                return size
    raise AssertionError("Full unit group should cover all starting points")


def check_cycles():
    cases = 0
    for modulus in (3, 5, 7, 9, 11, 13, 17, 19, 25):
        units = unit_group(modulus)
        for a, k in product((2, 3, 5), (1, 2, 3, 4)):
            if gcd(a, modulus) != 1:
                continue
            if k == 1:
                # Every start then requires its own mark.
                continue
            multipliers = {pow(a, i, modulus) for i in range(k)}
            got = minimum_cover(units, multipliers, modulus)
            d = order(a, modulus)
            expected = (len(units) // d) * ((d + k - 1) // k)
            assert got == expected, (modulus, a, k, got, expected)
            cases += 1
    return cases


def check_mixed_orbits():
    # A mixed tuple is encoded by the exponent of each root relative to
    # one root of order 9. 3,6 have order 3; units have order 9.
    units = unit_group(9)
    matches = 0
    for vector in product(range(1, 9), repeat=3):
        orbit = {tuple(u * a % 9 for a in vector) for u in units}
        largest_order = max(9 // gcd(a, 9) for a in vector)
        assert len(orbit) == len(unit_group(largest_order))
        matches += 1
    return matches


if __name__ == "__main__":
    print(f"Geometric-progression covers exhaustively verified: {check_cycles()}")
    print(f"Mixed tuples with verified unit orbit sizes: {check_mixed_orbits()}")
    p = 7
    costs = []
    for h in (1, 2, 3):
        d = order(2, p**h)
        costs.append(Fraction((d + 1) // 2, d))
    assert costs == [Fraction(2, 3), Fraction(11, 21), Fraction(74, 147)]
    assert sum(costs[:2]) == Fraction(25, 21)
    print("At p=7, shell costs:", ", ".join(map(str, costs)))
    print("At p=7, exact one-variable cost at levels 1 and 2:", sum(costs[:2]))
