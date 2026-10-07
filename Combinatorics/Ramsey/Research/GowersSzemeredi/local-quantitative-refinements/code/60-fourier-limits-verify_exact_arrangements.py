#!/usr/bin/env python3
"""Exact finite checks for the all-order arrangement profile.

All arithmetic used in theorem comparisons is rational or integer. These checks
are diagnostics for the accompanying written proof, not a proof of its generality.
The code handles cyclic coordinate and target groups, with repeated queries kept.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb, isqrt
from pathlib import Path
import json


def convolution(a, b, n, q):
    c = [0] * (n * q)
    for i, ai in enumerate(a):
        if not ai:
            continue
        x, z = divmod(i, q)
        for j, bj in enumerate(b):
            if bj:
                y, w = divmod(j, q)
                c[((x + y) % n) * q + (z + w) % q] += ai * bj
    return c


def relation_failure(table, n, labels, q, s):
    counts = [0] * (n * q)
    for x in range(n):
        for y in range(labels):
            counts[x * q + table[x * labels + y]] += 1
    conv = [0] * (n * q)
    conv[0] = 1
    for _ in range(s // 2):
        conv = convolution(conv, counts, n, q)
    accepted = sum(v * v for v in conv)
    total = n ** (s - 1) * labels ** s
    return 1 - Q(accepted, total)


def derivative(table, n, hsize, q, shift):
    return tuple((table[x * hsize + (y + shift) % hsize]
                  - table[x * hsize + y]) % q
                 for x in range(n) for y in range(hsize))


def arrangement_failure(table, n, hsize, q, s):
    return sum(relation_failure(derivative(table, n, hsize, q, h),
                                n, hsize, q, s)
               for h in range(hsize)) / hsize


def E(s, t):
    return (1 - (1 - 2 * t) ** s) / 2 - 2 ** (s - 1) * t ** (s - 1) * (1 - t)


def B(s, d):
    return E(s, 2 * d) / 2


def nearest_model(table, n, hsize, q):
    best = n * hsize + 1
    best_parameters = None
    for b in range(q):
        if n * b % q or hsize * b % q:
            continue
        for c in range(q):
            if hsize * c % q:
                continue
            errors = 0
            row_modes = []
            for x in range(n):
                residual = [(table[x * hsize + y] - b * x * y - c * y) % q
                            for y in range(hsize)]
                counts = Counter(residual)
                mode, count = max(counts.items(), key=lambda a: (a[1], -a[0]))
                errors += hsize - count
                row_modes.append(mode)
            if errors < best:
                best = errors
                best_parameters = b, c, row_modes
    b, c, row_modes = best_parameters
    residual = tuple((table[x * hsize + y] - b * x * y - c * y
                      - row_modes[x]) % q
                     for x in range(n) for y in range(hsize))
    return Q(best, n * hsize), residual


def transpose(table, n, hsize):
    return tuple(table[x * hsize + y] for y in range(hsize) for x in range(n))


def nearest_biaffine(table, n, hsize, q):
    best = n * hsize + 1
    best_residual = None
    for b in range(q):
        if n * b % q or hsize * b % q:
            continue
        for u in range(q):
            if n * u % q:
                continue
            for v in range(q):
                if hsize * v % q:
                    continue
                residual = tuple((table[x * hsize + y] - b * x * y - u * x - v * y) % q
                                 for x in range(n) for y in range(hsize))
                mode, count = max(Counter(residual).items(), key=lambda a: (a[1], -a[0]))
                if n * hsize - count < best:
                    best = n * hsize - count
                    best_residual = tuple((z - mode) % q for z in residual)
    return Q(best, n * hsize), best_residual


def is_cyclic_coset(support, n):
    if not support:
        return False
    for index in range(1, n + 1):
        if n % index:
            continue
        for base in range(index):
            if support == {x for x in range(n) if x % index == base}:
                return True
    return False


def auxiliary_equality_shape(table, n, labels, q):
    values = {z for z in table if z}
    if len(values) != 1:
        return False
    a = next(iter(values))
    if 2 * a % q:
        return False
    support = set()
    for x in range(n):
        row = table[x * labels:(x + 1) * labels]
        if len(set(row)) != 1:
            return False
        if row[0]:
            support.add(x)
    return is_cyclic_coset(support, n)


def arrangement_equality_shape(residual, n, hsize, q):
    if hsize % 2 or q % 2:
        return False
    first = derivative(residual, n, hsize, q, 1)
    if not auxiliary_equality_shape(first, n, hsize, q):
        return False
    support = {x for x in range(n) if first[x * hsize]}
    if 2 * len(support) >= n:
        return False
    a = q // 2
    return all((residual[x * hsize + y] - residual[x * hsize]) % q
               == (a * (x in support) * (y % 2)) % q
               for x in range(n) for y in range(hsize))


def interval_energy(p, size, half_order):
    """Balanced 2m-tuple count on a cyclic interval, by bounded compositions."""
    counts = [0] * p
    for total in range(half_order * (size - 1) + 1):
        coefficient = sum((-1) ** j * comb(half_order, j)
                          * comb(total - j * size + half_order - 1, half_order - 1)
                          for j in range(min(half_order, total // size) + 1))
        counts[total % p] += coefficient
    return sum(v * v for v in counts)


def rho_moments(p, max_order):
    upper = (p - 1) // 2
    sums = [upper]
    for j in range(1, max_order + 1):
        numerator = (upper + 1) ** (j + 1) - 1
        numerator -= sum(comb(j + 1, k) * sums[k] for k in range(j))
        assert numerator % (j + 1) == 0
        sums.append(numerator // (j + 1))
    return [Q(1)] + [Q(2 ** (j + 1) * sums[j], p ** (j + 1))
                     for j in range(1, max_order + 1)]


def prime_obstruction_error(p, size, s):
    """Exact formula; p>s excludes vertical wrap in moments up to s."""
    assert p > s
    r = Q(size, p)
    moments = rho_moments(p, s)
    assert moments[1] == Q(p * p - 1, 2 * p * p)
    assert moments[2] == Q(p * p - 1, 3 * p * p)
    defect = sum((-1) ** (j + 1) * comb(s, j) * r ** j
                 * Q(comb(2 * j, j), 2 ** j) * moments[j]
                 for j in range(1, s))
    defect -= (Q(comb(2 * s, s), 2 ** s)
               * Q(interval_energy(p, size, s // 2), p ** (s - 1)) * moments[s])
    return defect


def run():
    report = {
        "arithmetic": "exact integers and fractions.Fraction",
        "proof_status": "finite diagnostics only; universal results use written proofs",
        "orders": [4, 6, 8, 16],
        "auxiliary_suites": [],
        "arrangement_suites": [],
        "coset_examples": [],
        "two_direction_suites": [],
        "intersection_examples": [],
        "prime_quadratic_obstructions": [],
        "odd_target_suites": [],
    }
    orders = report["orders"]
    suites = [(3, 2, 2), (4, 2, 2), (5, 2, 2),
              (3, 3, 2), (3, 2, 3), (2, 3, 3), (2, 2, 3),
              (3, 2, 4), (3, 4, 2), (6, 2, 2), (2, 2, 5)]
    for n, labels, q in suites:
        compared = equalities = 0
        for table in product(range(q), repeat=n * labels):
            t = Q(sum(z != 0 for z in table), n * labels)
            if not 0 < t < Q(1, 2):
                continue
            expected_equality = auxiliary_equality_shape(table, n, labels, q)
            for s in orders:
                defect = relation_failure(table, n, labels, q, s)
                bound = E(s, t)
                assert defect >= bound, ("auxiliary bound", n, labels, q, table, s)
                assert (defect == bound) == expected_equality, (
                    "auxiliary equality", n, labels, q, table, s)
                compared += 1
                equalities += defect == bound
        report["auxiliary_suites"].append(dict(n=n, labels=labels, q=q,
                                                comparisons=compared, equalities=equalities))
    for n, labels, q in suites:
        if q % 2 == 0:
            continue
        compared = 0
        for table in product(range(q), repeat=n * labels):
            nonzero = Counter(z for z in table if z)
            total_nonzero = sum(nonzero.values())
            t = Q(total_nonzero, n * labels)
            if total_nonzero:
                c = sum(Q(count, total_nonzero) ** 2 for count in nonzero.values())
                inverse = sum(Q(count * nonzero.get((-z) % q, 0), total_nonzero ** 2)
                              for z, count in nonzero.items())
                assert c + inverse <= 1
            else:
                c = inverse = Q(0)
            for s in orders:
                defect = relation_failure(table, n, labels, q, s)
                C = Q(s * (3 * s - 2), 4)
                D = (s * s + 1) * comb(s, 3)
                coefficient = Q(comb(s, 2)) + (s // 2) ** 2 * c
                coefficient += (s // 2) * (s // 2 - 1) * inverse
                assert abs(defect - s * t + coefficient * t ** 2) <= D * t ** 3
                assert defect >= s * t - C * t ** 2 - D * t ** 3
                compared += 1
        report["odd_target_suites"].append(dict(n=n, labels=labels, q=q,
                                                 comparisons=compared))
    for n, hsize, q in suites:
        compared = equalities = 0
        for table in product(range(q), repeat=n * hsize):
            d, residual = nearest_model(table, n, hsize, q)
            if not 0 < d < Q(1, 4):
                continue
            expected_equality = arrangement_equality_shape(residual, n, hsize, q)
            t_profile = [Q(sum(z != 0 for z in derivative(residual, n, hsize, q, h)),
                           n * hsize) for h in range(hsize)]
            tbar = sum(t_profile) / hsize
            assert all(t <= 2 * d for t in t_profile)
            assert tbar >= d
            for s in orders:
                defect = arrangement_failure(table, n, hsize, q, s)
                bound = B(s, d)
                assert defect >= tbar / d * bound >= bound, (
                    "arrangement bound", n, hsize, q, table, s)
                assert (defect == bound) == expected_equality, (
                    "arrangement equality", n, hsize, q, table, s, d, defect, bound)
                compared += 1
                equalities += defect == bound
        report["arrangement_suites"].append(dict(n=n, hsize=hsize, q=q,
                                                  comparisons=compared, equalities=equalities))
    for n, hsize, q in suites:
        intersection_compared = local_compared = 0
        for table in product(range(q), repeat=n * hsize):
            transposed = transpose(table, n, hsize)
            dv, _ = nearest_model(table, n, hsize, q)
            dh, _ = nearest_model(transposed, hsize, n, q)
            d, residual = nearest_biaffine(table, n, hsize, q)
            eta = dv + dh
            if eta < Q(1, 4):
                # d<=J(eta) without evaluating an irrational square root.
                remainder = 1 + eta - 2 * d
                assert remainder >= 0 and remainder ** 2 >= 1 - 2 * eta, (
                    "robust intersection", n, hsize, q, table, eta, d)
                intersection_compared += 1
            if not 0 < d < Q(1, 4):
                continue
            horizontal_residual = transpose(residual, n, hsize)
            tv = sum(Q(sum(z != 0 for z in derivative(residual, n, hsize, q, h)),
                       n * hsize) for h in range(hsize)) / hsize
            th = sum(Q(sum(z != 0 for z in derivative(horizontal_residual, hsize, n, q, g)),
                       n * hsize) for g in range(n)) / n
            assert tv + th >= 2 * d * (1 - d), ("Efron-Stein", table)
            for s in orders:
                ev = arrangement_failure(table, n, hsize, q, s)
                eh = arrangement_failure(transposed, hsize, n, q, s)
                assert ev + eh >= 2 * (1 - d) * B(s, d), (
                    "two-direction local", n, hsize, q, table, s, d)
                local_compared += 1
        report["two_direction_suites"].append(dict(n=n, hsize=hsize, q=q,
                                                    intersection_comparisons=intersection_compared,
                                                    local_comparisons=local_compared))
    for n in range(3, 25):
        table = tuple((x == 0) * y for x in range(n) for y in range(2))
        d, residual = nearest_model(table, n, 2, 2)
        assert d == Q(1, 2 * n)
        for s in [4, 6, 8, 16]:
            defect = arrangement_failure(table, n, 2, 2, s)
            assert defect == B(s, d)
        report["coset_examples"].append(dict(n=n, distance=str(d),
                                               orders=[4, 6, 8, 16]))
    for n in [7, 9, 11, 13, 15, 17]:
        u = Q(1, n)
        table = tuple(int(x == 0 or y == 0) for x in range(n) for y in range(n))
        dv, _ = nearest_model(table, n, n, 2)
        dh, _ = nearest_model(transpose(table, n, n), n, n, 2)
        d, _ = nearest_biaffine(table, n, n, 2)
        assert dv == dh == u * (1 - u)
        assert d == 2 * u - u ** 2
        eta = dv + dh
        assert (1 + eta - 2 * d) ** 2 == 1 - 2 * eta
        report["intersection_examples"].append(dict(n=n, eta=str(eta), distance=str(d)))
    # Cross-check the exact symbolic prime formula by the generic 2D integer
    # convolution counter, before using it for larger examples.
    p = 17
    size = isqrt(p)
    table = tuple(int(x < size and y < (p - 1) // 2) for x in range(p) for y in range(p))
    for s in orders:
        assert prime_obstruction_error(p, size, s) == arrangement_failure(table, p, p, p, s)
    for p in [101, 10007, 1000003]:
        assert all(p % divisor for divisor in range(2, isqrt(p) + 1))
        size = isqrt(p)
        r = Q(size, p)
        d = r * Q(p - 1, 2 * p)
        for s in orders:
            defect = prime_obstruction_error(p, size, s)
            moments = rho_moments(p, s)
            approximation = s * r * moments[1] - Q(3, 4) * s * (s - 1) * r ** 2 * moments[2]
            error_bound = (s * s + 1) * comb(s, 3) * r ** 3
            assert abs(defect - approximation) <= error_bound
            normalized_second_coefficient = (s * d - defect) / d ** 2
            report["prime_quadratic_obstructions"].append(dict(
                p=p, rows=size, s=s, distance=str(d), error=str(defect),
                normalized_second_coefficient=str(normalized_second_coefficient),
                displayed_second_coefficient=float(normalized_second_coefficient),
                limiting_second_coefficient=s * (s - 1),
                proved_uniform_remainder_bound=str(error_bound)))
    report["total_auxiliary_comparisons"] = sum(x["comparisons"] for x in report["auxiliary_suites"])
    report["total_arrangement_comparisons"] = sum(x["comparisons"] for x in report["arrangement_suites"])
    report["total_auxiliary_equalities"] = sum(x["equalities"] for x in report["auxiliary_suites"])
    report["total_arrangement_equalities"] = sum(x["equalities"] for x in report["arrangement_suites"])
    report["total_intersection_comparisons"] = sum(x["intersection_comparisons"] for x in report["two_direction_suites"])
    report["total_two_direction_comparisons"] = sum(x["local_comparisons"] for x in report["two_direction_suites"])
    report["total_odd_target_comparisons"] = sum(x["comparisons"] for x in report["odd_target_suites"])
    destination = Path(__file__).with_name("verification_exact_arrangements.json")
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k.startswith("total_")}, indent=2))


if __name__ == "__main__":
    run()
