"""Exact finite checks of the two discrete identities in the microscopic proof.

Run with Python 3. Every arithmetic operation on a divided difference or an
atom position uses fractions.Fraction or integers.
"""
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, prod


def interpolation_weight(nodes, x):
    if x not in nodes:
        return Fraction(0)
    return Fraction(1, prod(x - y for y in nodes if y != x))


@lru_cache(None)
def consecutive_weights(nodes):
    left, right = nodes[0], nodes[-1]
    if right - left == len(nodes) - 1:
        return {left: Fraction(1)}
    y = next(x for x in range(left + 1, right) if x not in nodes)
    weights = defaultdict(Fraction)
    for shorter, factor in [
        (nodes[:-1] + (y,), Fraction(y - left, right - left)),
        (nodes[1:] + (y,), Fraction(right - y, right - left)),
    ]:
        for j, v in consecutive_weights(tuple(sorted(shorter))).items():
            weights[j] += factor * v
    return dict(weights)


def check_interpolation():
    count = 0
    for r in range(1, 6):
        for nodes in combinations(range(9), r + 1):
            weights = consecutive_weights(nodes)
            assert all(w >= 0 for w in weights.values())
            assert sum(weights.values()) == 1
            # Testing all delta functions proves equality of the linear
            # functionals on this grid, for every possible vector of values.
            for x in range(9):
                value = sum(w * (-1)**(r - (x-j)) * comb(r, x-j)
                            for j, w in weights.items() if j <= x <= j+r)
                assert Fraction(value, factorial(r)) == interpolation_weight(nodes, x)
            count += 1
    print(f"Convex divided-difference identity: {count} choices of nodes,")
    print("orders 1 through 5 on {0,...,8}, checked on all 9 basis vectors.")


def check_bins():
    # Two atomic locations inside each bin, one exactly at the left endpoint.
    # These counts have both a low and a high in every three-bin block.
    data = [2, 6, 2, 5, 2, 2, 6, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4, 2]
    h = Fraction(2, 3)
    atoms = {}
    for n, count in enumerate(data):
        atoms[n*h] = 1
        atoms[n*h+h/4] = count-1

    total_bins = 0
    for r in range(1, 6):
        signed = defaultdict(int)
        for location, mult in atoms.items():
            for j in range(r+1):
                signed[location-j*h] += (-1)**(r-j) * comb(r, j) * mult
        bin_mass = defaultdict(int)
        for location, mult in signed.items():
            bin_mass[location // h] += mult
        for n in range(-r-1, len(data)+1):
            difference = sum((-1)**(r-j) * comb(r, j) * data[n+j]
                             for j in range(r+1) if 0 <= n+j < len(data))
            assert difference == bin_mass[n]
            total_bins += 1
        # Choose low/high in alternation, once for each target sign. Require
        # matching signs of an actual bin mass and an individual atom in it.
        for sign in (-1, 1):
            nodes = tuple(next(n for n in range(3*j, 3*j+3)
                               if sign * (-1)**(r-j) * (data[n]-3) > 0)
                          for j in range(r+1))
            direct = sum(data[n]*interpolation_weight(nodes, n) for n in nodes)
            assert sign * direct > 0
            witness = next(n for n in range(nodes[0], nodes[-1]-r+1)
                           if sign * bin_mass[n] > 0)
            assert any(location // h == witness and sign * mass > 0
                       for location, mass in signed.items())
    print(f"Translated atomic divisor and bin counts: {total_bins} bin identities,")
    print("including endpoint atoms and partial overlap of translates.")
    print("Alternating nodes yield both signs of actual atoms for each order 1 to 5.")


if __name__ == "__main__":
    check_interpolation()
    check_bins()
