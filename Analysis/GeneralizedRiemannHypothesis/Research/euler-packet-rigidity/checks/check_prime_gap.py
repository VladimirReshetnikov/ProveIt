"""Check exact equality ratios by direct counts of projected multisets.

For each tested odd p, affine changes of coordinates take every first
two-point set in F_p^2 to {(0,0),(1,0)}. All disjoint choices of the
second two-point set are then enumerated. General-rank claims are proved
in the paper; the finite checks illustrate their planar equality cases.
"""
from fractions import Fraction
from itertools import combinations, product


def projections(packet, u, v, p):
    return sorted((u * x + v * y) % p for x, y in packet)


def density(left, right, prime):
    directions = [(0, 1)] + [(1, slope) for slope in range(prime)]
    different = sum(projections(left, *v, prime) != projections(right, *v, prime)
                    for v in directions)
    return Fraction((prime - 1) * different, prime ** 2)


def parallelogram(left, right, p):
    sums_agree = all((sum(a[i] for a in left) - sum(b[i] for b in right)) % p == 0
                     for i in range(2))
    ((x1, y1), (x2, y2)) = right
    independent = (x1 * y2 - x2 * y1) % p != 0  # first positive point is (0,0)
    return sums_agree and independent


def main():
    for p in (3, 5, 7, 11):
        plane = set(product(range(p), repeat=2))
        first = {(0, 0), (1, 0)}
        target_ratio = Fraction(2 * (p-1), p)
        peak = 0
        total = 0
        for second in combinations(sorted(plane - first), 2):
            ratio = density(first, second, p) / Fraction(p - 1, 2 * p)
            assert ratio >= target_ratio
            assert (ratio == target_ratio) == parallelogram(first, second, p)
            peak += (ratio == target_ratio)
            total += 1
        assert peak == p * (p - 1) // 2
        x_arm = {(a, 0) for a in range(1, p)}
        y_arm = {(0, a) for a in range(1, p)}
        arms = density(x_arm, y_arm, p)
        assert arms == Fraction(2 * (p-1), p**2)
        assert arms / Fraction(1, p) == target_ratio
        print(f"p={p} | normalized two-set pairs {total} | parallelograms {peak} "
              f"| least ratio {target_ratio} | punctured-line density {arms}")
    print("All assertions passed.")


if __name__ == '__main__':
    main()
