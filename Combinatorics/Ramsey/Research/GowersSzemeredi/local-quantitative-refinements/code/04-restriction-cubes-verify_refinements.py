#!/usr/bin/env python3
"""Finite checks for 'Sharper Local Bounds in Gowers's Proof'.

Uses only the Python standard library. These checks supplement the mathematical
proofs; they do not establish the infinite families of statements by themselves.
Run: python3 verify_refinements.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
from collections import Counter
from fractions import Fraction


def rank(rows, prime=None):
    """Exact row rank over Q, or a prime field."""
    if not rows:
        return 0
    if prime is None:
        a = [[Fraction(x) for x in row] for row in rows]
    else:
        a = [[x % prime for x in row] for row in rows]
    nr, nc, pivot = len(a), len(a[0]), 0
    for col in range(nc):
        pick = next((j for j in range(pivot, nr) if a[j][col]), None)
        if pick is None:
            continue
        a[pivot], a[pick] = a[pick], a[pivot]
        factor = (1 / a[pivot][col] if prime is None
                  else pow(a[pivot][col], -1, prime))
        a[pivot] = [x * factor for x in a[pivot]]
        if prime is not None:
            a[pivot] = [x % prime for x in a[pivot]]
        for j in range(nr):
            if j == pivot or not a[j][col]:
                continue
            fac = a[j][col]
            a[j] = [x - fac * y for x, y in zip(a[j], a[pivot])]
            if prime is not None:
                a[j] = [x % prime for x in a[j]]
        pivot += 1
        if pivot == nr:
            break
    return pivot


def cube_support_counts(d, prime=None):
    vertices = list(itertools.product((0, 1), repeat=d))
    rows = [(1,) + v for v in vertices]
    result = [0] * (len(vertices) + 1)
    for mask in range(1 << len(vertices)):
        sub = [rows[i] for i in range(len(rows)) if mask >> i & 1]
        full = rank(sub, prime)
        if all(rank(sub[:i] + sub[i + 1:], prime) == full
               for i in range(len(sub))):
            result[len(sub)] += 1
    return result


def parallelogram_count(d):
    verts = list(itertools.product((0, 1), repeat=d))
    pairs = Counter(tuple(x + y for x, y in zip(a, b))
                    for a, b in itertools.combinations(verts, 2))
    # Two different pairs with the same midpoint have four distinct vertices.
    return sum(math.comb(m, 2) for m in pairs.values())


def convolution_graph_energy(n, graph, max_order=8):
    counts = {(0, 0): 1}
    energies = []
    for _ in range(max_order):
        new = Counter()
        for (x, y), multiplicity in counts.items():
            for a, b in graph:
                new[((x + a) % n, (y + b) % n)] += multiplicity
        counts = new
        energies.append(sum(v * v for v in counts.values()))
    return energies


def graph_energy_checks():
    checked = inequalities = 0
    equality_cases = 0
    for n in range(2, 6):
        # Value -1 means the point is absent from the domain.
        for values in itertools.product(range(-1, n), repeat=n):
            graph = [(i, y) for i, y in enumerate(values) if y >= 0]
            if not graph:
                continue
            es = convolution_graph_energy(n, graph)
            m = len(graph)
            assert es[0] == m
            for d in range(2, 9):
                left = es[d - 1] * m ** (d - 2)
                right = es[1] ** (d - 1)
                assert left >= right, (n, graph, d)
                inequalities += 1
                equality_cases += left == right
            checked += 1
    return {"nonempty_graphs": checked, "exact_inequalities": inequalities,
            "equalities": equality_cases, "cyclic_orders": [2, 3, 4, 5],
            "moment_orders": list(range(2, 9))}


def fourier(f):
    n = len(f)
    return [sum(f[x] * cmath.exp(-2j * math.pi * r * x / n)
                for x in range(n)) / n for r in range(n)]


def cube_form(f, d):
    n = len(f)
    vertices = list(itertools.product((0, 1), repeat=d))
    total = 0j
    for hs in itertools.product(range(n), repeat=d):
        for x in range(n):
            product = 1 + 0j
            for v in vertices:
                y = (x + sum(a * b for a, b in zip(v, hs))) % n
                z = complex(f[y])
                product *= z.conjugate() if sum(v) % 2 else z
            total += product
    return total / n ** (d + 1)


def cube_numeric_checks():
    rng = random.Random(20261006)
    largest_identity_error = 0.0
    largest_cosine_error = 0.0
    smallest_gap_ratio = float("inf")
    count = 0
    for n in [3, 5, 7, 9, 11]:
        for _ in range(8):
            f = [rng.uniform(-1, 1) for _ in range(n)]
            avg = sum(f) / n
            f = [x - avg for x in f]
            F = fourier(f)
            S = sum(abs(z) ** 4 for z in F)
            u8 = cube_form(f, 3).real
            spectral = sum(abs(sum(F[r] * F[(r + a) % n].conjugate()
                                  * F[(r + b) % n].conjugate()
                                  * F[(r + a + b) % n]
                                  for r in range(n))) ** 2
                           for a in range(n) for b in range(n))
            largest_identity_error = max(largest_identity_error,
                                         abs(u8 - spectral))
            assert abs(u8 - spectral) < 2e-11
            assert u8 + 2e-11 >= 2 * S * S
            smallest_gap_ratio = min(smallest_gap_ratio, u8 / (S * S))
            count += 1
        delta, t = 0.4, 0.2
        f = [t * math.cos(2 * math.pi * x / n) for x in range(n)]
        w = [delta + x for x in f]
        u8 = cube_form(f, 3).real
        assert abs(u8 - t ** 8 / 32) < 2e-11
        if n > 8:
            expected = delta ** 8 + 1.5 * delta ** 4 * t ** 4 + t ** 8 / 32
            error = abs(cube_form(w, 3).real - expected)
            largest_cosine_error = max(largest_cosine_error, error)
            assert error < 2e-11
        if n == 3:
            expected = (delta ** 8 + 1.5 * delta ** 4 * t ** 4
                        + 0.5 * delta ** 3 * t ** 5
                        + 0.5 * delta ** 2 * t ** 6 + t ** 8 / 32)
            error = abs(cube_form(w, 3).real - expected)
            largest_cosine_error = max(largest_cosine_error, error)
            assert error < 2e-11
    return {"random_real_centered_functions": count,
            "largest_fourier_identity_error": largest_identity_error,
            "smallest_random_gap_ratio": smallest_gap_ratio,
            "largest_cosine_formula_error": largest_cosine_error,
            "numeric_tolerance": 2e-11}


def kernel_checks():
    rows = []
    for d in [2, 3, 8]:
        for a in [Fraction(1), Fraction(1, 2), Fraction(1, 5)]:
            L = math.ceil(4 / a)
            q = 4 * d * L * L
            ratio = Fraction(1)
            min_power = Fraction(1)
            for ell in range(1, L + 1):
                ratio *= Fraction(q - ell + 1, q + ell)
                assert ratio >= 1 - Fraction(ell * ell, q)
                assert ratio ** (2 * d) >= Fraction(1, 2)
                min_power = min(min_power, ratio ** (2 * d))
            c = a ** (2 * d) / (2 * (400 * d) ** d)
            assert c <= a / 2
            assert q <= 100 * d / (a * a)
            rows.append({"d": d, "a": str(a), "L": L, "q": q,
                         "minimum_retained_ratio_power": float(min_power)})
    # Exact integer checks for the clean d=8 powers of two.
    assert 2 * 3200 ** 8 < 2 ** 95
    assert 2 * (1 + math.comb(16, 2)) * 3200 ** 8 < 2 ** 102
    # Central binomial lower bound c0 >= 1/(2 sqrt(q)), squared.
    for q in range(1, 501):
        c0 = Fraction(math.comb(2 * q, q), 4 ** q)
        assert 4 * q * c0 * c0 >= 1
    return {"ratio_cases": rows, "central_binomial_cases": 500,
            "order_eight_retention_exponent": 95,
            "order_eight_size_exponent": 102,
            "order_eight_gamma_threshold_exponent": 112,
            "order_eight_eta_threshold_exponent": 16,
            "order_eight_density_threshold_exponent": 1}


def progression_checks():
    rng = random.Random(9317)
    examples = 0
    max_difference = 0.0
    for n, slopes in [(5, [0, 1, 2, 3]), (7, [0, 1, 3, 5]),
                      (25, [0, 1, 2])]:
        m = len(slopes)
        for _ in range(12):
            fs = [[rng.random() for _ in range(n)] for _ in range(m)]
            ds = [sum(f) / n for f in fs]

            def lam(indices, centered=None):
                return sum(math.prod((fs[i][(x + slopes[i] * y) % n] - ds[i]
                                      if i == centered
                                      else fs[i][(x + slopes[i] * y) % n])
                                     for i in indices)
                           for x in range(n) for y in range(n)) / (n * n)
            actual = lam(range(m)) - math.prod(ds)
            telescope = sum(math.prod(ds[j + 1:])
                            * lam(range(j + 1), centered=j)
                            for j in range(2, m))
            err = abs(actual - telescope)
            assert err < 1e-12
            max_difference = max(max_difference, err)
            examples += 1
    return {"weighted_examples": examples,
            "maximum_telescoping_identity_error": max_difference}


def two_frequency_polynomial():
    """Exact U^3 polynomial of delta+a*cos(x)+b*cos(2*x), with no aliasing."""
    half = Fraction(1, 2)
    spec = {-2: ((0, 0, 1), half), -1: ((0, 1, 0), half),
            0: ((1, 0, 0), Fraction(1)),
            1: ((0, 1, 0), half), 2: ((0, 0, 1), half)}
    poly = Counter()
    for s, t in itertools.product(range(-4, 5), repeat=2):
        inner = Counter()
        for r in spec:
            indices = [r, r + s, r + t, r + s + t]
            if any(index not in spec for index in indices):
                continue
            degree = tuple(sum(spec[index][0][i] for index in indices)
                           for i in range(3))
            coefficient = math.prod(spec[index][1] for index in indices)
            inner[degree] += coefficient
        for da, ca in inner.items():
            for db, cb in inner.items():
                poly[tuple(a + b for a, b in zip(da, db))] += ca * cb
    expected = {(8, 0, 0): Fraction(1),
                (4, 4, 0): Fraction(3, 2),
                (4, 0, 4): Fraction(3, 2),
                (3, 4, 1): Fraction(1, 2),
                (2, 4, 2): Fraction(3, 2),
                (0, 8, 0): Fraction(1, 32),
                (0, 4, 4): Fraction(3, 16),
                (0, 0, 8): Fraction(1, 32)}
    assert dict(poly) == expected
    return [{"powers_delta_a_b": list(degree), "coefficient": str(coef)}
            for degree, coef in sorted(poly.items(), reverse=True)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default="verification_results.json")
    ap.add_argument("--skip-exhaustive", action="store_true")
    args = ap.parse_args()
    supports = {}
    for p in [None, 2, 3, 5, 7]:
        got = cube_support_counts(3, p)
        want = ([1, 0, 0, 0, 14, 0, 28, 8, 1] if p == 2
                else [1, 0, 0, 0, 12, 8, 28, 8, 1])
        assert got == want, (p, got)
        supports["Q" if p is None else f"F_{p}"] = got
    parallelograms = {}
    for d in range(2, 8):
        value = parallelogram_count(d)
        formula = Fraction(2) ** (d - 3) * (3 ** d - 2 ** (d + 1) + 1)
        assert value == formula
        parallelograms[d] = value
    result = {
        "status": "passed",
        "purpose": "Supplementary finite checks, not substitutes for proofs.",
        "cube_support_counts": supports,
        "parallelogram_counts": parallelograms,
        "kernel": kernel_checks(),
        "cube_numeric": cube_numeric_checks(),
        "progression_numeric": progression_checks(),
        "two_frequency_exact_polynomial": two_frequency_polynomial(),
    }
    if not args.skip_exhaustive:
        result["graph_energy"] = graph_energy_checks()
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
