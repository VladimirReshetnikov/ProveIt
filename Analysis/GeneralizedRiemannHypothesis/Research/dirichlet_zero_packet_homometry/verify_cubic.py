#!/usr/bin/env python3
"""Check the single-cubic reconstruction theorem on finite integer histograms.

All computations take place in Z[x]/(1+x+...+x^(ell-1)).
Run with Python 3.8 or later. No third-party dependencies are needed.
"""

from collections import Counter
from itertools import combinations_with_replacement
from math import comb


def cubic_key(points, ell):
    """Coefficients of alpha^2 * conjugate(sigma_2(alpha)) in the power basis."""
    counts = Counter((u + v - 2 * w) % ell for u in points for v in points for w in points)
    return tuple(counts[j] - counts[ell - 1] for j in range(ell - 1))


def quadratic_keys(points, ell):
    """Power-basis keys of all products alpha(k) * conjugate(alpha(k))."""
    keys = []
    for k in range(ell):
        counts = Counter((k * (u - v)) % ell for u in points for v in points)
        keys.append(tuple(counts[j] - counts[ell - 1] for j in range(ell - 1)))
    return tuple(keys)


def orbit_key(points, ell):
    counts = Counter(points)
    return min(tuple(counts[(j + shift) % ell] for j in range(ell)) for shift in range(ell))


def check(ell, rank):
    orbit_by_cubic = {}
    cubic_by_orbit = {}
    checked = 0
    for points in combinations_with_replacement(range(ell), rank):
        cubic = cubic_key(points, ell)
        orbit = orbit_key(points, ell)
        if orbit_by_cubic.setdefault(cubic, orbit) != orbit:
            raise ValueError(f"Two orbits share a cubic at ell={ell}, rank={rank}")
        if cubic_by_orbit.setdefault(orbit, cubic) != cubic:
            raise ValueError(f"Rotation changes the cubic at ell={ell}, rank={rank}")
        checked += 1
    expected = comb(ell + rank - 1, rank)
    if checked != expected:
        raise ValueError(f"Enumerated {checked} histograms, expected {expected}")
    return checked, len(orbit_by_cubic)


if __name__ == "__main__":
    print("All histograms of each prescribed rank, counted before taking rotations")
    for ell in [3, 5, 7]:
        for rank in range(6):
            checked, orbit_count = check(ell, rank)
            print(f"ell={ell}  rank={rank}  histograms={checked:3d}  cubic values=orbits={orbit_count}")
    print("Reflection test for the multiset {0,1,1} and its negative")
    for ell in [3, 5, 7]:
        points = (0, 1, 1)
        reflected = tuple((-u) % ell for u in points)
        cubic_a = cubic_key(points, ell)
        cubic_b = cubic_key(reflected, ell)
        if quadratic_keys(points, ell) != quadratic_keys(reflected, ell):
            raise ValueError(f"Quadratic products disagree at ell={ell}")
        if cubic_a == cubic_b or orbit_key(points, ell) == orbit_key(reflected, ell):
            raise ValueError(f"Reflection unexpectedly preserved the orbit or cubic at ell={ell}")
        print(f"ell={ell}  all quadratic products agree  cubic={cubic_a}  reflected cubic={cubic_b}")
