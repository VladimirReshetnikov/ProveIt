"""Finite checks for the construction in progressions.tex (standard library)."""

from fractions import Fraction
from itertools import product
from math import prod


def greedy_exponents(k, bound):
    accepted = set()
    for end in range(bound + 1):
        rejected = any(
            all(end - j * step in accepted for j in range(1, k))
            for step in range(1, end // (k - 1) + 1)
        )
        if not rejected:
            accepted.add(end)
    return accepted


def edited_box(k, good, satellite_count):
    b = k - 2
    original = set(product(good, repeat=satellite_count + 1))
    changed = set()
    for point in original:
        satellites = point[1:]
        deviations = [e for e in satellites if e != b]
        if not deviations or (len(deviations) == 1 and deviations[0] >= k):
            continue
        changed.add(point)

    for i in range(satellite_count):
        satellite = [b] * satellite_count
        satellite[i] = k - 1
        changed.add((k - 1, *satellite))
    return original, changed


def directed_progressions(k, bound, dimension):
    # Endpoints are in the box exactly when the signed step and start
    # lie within the coordinate ranges below.
    max_step = bound // (k - 1)
    for step in product(range(-max_step, max_step + 1), repeat=dimension):
        if not any(step):
            continue
        starts = [
            range(max(0, -(k - 1) * d), min(bound, bound - (k - 1) * d) + 1)
            for d in step
        ]
        for first in product(*starts):
            yield first, step


def check(k, bound):
    primes = (2, 3, 5)
    good = greedy_exponents(k, bound)
    old, changed = edited_box(k, good, len(primes) - 1)
    examined = 0
    for first, step in directed_progressions(k, bound, len(primes)):
        examined += 1
        if first not in changed:
            continue
        assert any(
            tuple(a + j * d for a, d in zip(first, step)) not in changed
            for j in range(1, k)
        )

    def weight(point):
        denominator = prod(p**e for p, e in zip(primes, point))
        return Fraction(1, denominator)

    difference = sum(map(weight, changed - old)) - sum(map(weight, old - changed))
    marker, *satellites = primes
    b = k - 2
    reference_weight = Fraction(1, prod(q**b for q in satellites))
    additions = Fraction(1, marker ** (k - 1)) * sum(
        Fraction(1, q) for q in satellites
    )
    deletion_factor = 1 + sum(
        Fraction(1, q ** (e - b)) for q in satellites for e in good if e >= k
    )
    marker_mass = sum(Fraction(1, marker**e) for e in good)
    assert difference == reference_weight * (additions - deletion_factor * marker_mass)
    print(f"k={k}  box=[0,{bound}]^3  directed_progressions={examined}  "
          f"surviving_points={len(changed)}  mass_identity=exact")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so all checks are active.")
    for length in range(3, 10):
        check(length, 2 * length + 1)
