#!/usr/bin/env python3
"""Exact certificates for prime torsion in Boolean configurations.

Python standard library only.  No floating-point decision is used.
Run from any directory: python3 code/verify_torsion.py
The optional --regenerate flag recreates the finite nonexistence witnesses.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import gcd, lcm
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]


def determinant(matrix):
    """Fraction-free elimination, with exact-divisibility assertions."""
    a = [list(row) for row in matrix]
    n = len(a)
    assert all(len(row) == n for row in a)
    if not n:
        return 1
    previous = sign = 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        diagonal = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * diagonal - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = diagonal
    return sign * a[-1][-1]


def rational_nullvector(rows, columns):
    a = [[Fraction(x) for x in row] for row in rows]
    pivots = []
    r = 0
    for j in range(columns):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][j]
        a[r] = [x / scale for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][j]:
                scale = a[i][j]
                a[i] = [x - scale * y for x, y in zip(a[i], a[r])]
        pivots.append(j)
        r += 1
        if r == columns:
            return None, r
    free = next(j for j in range(columns) if j not in pivots)
    vector = [Fraction(int(j == free)) for j in range(columns)]
    for i, j in enumerate(pivots):
        vector[j] = -a[i][free]
    denominator = lcm(*(x.denominator for x in vector))
    integers = [int(x * denominator) for x in vector]
    common = gcd(*integers)
    integers = [x // common for x in integers]
    if next(x for x in integers if x) < 0:
        integers = [-x for x in integers]
    return integers, r


def zero_sum_masks(c, p):
    residues = [0]
    for x in c:
        residues += [(v + x) % p for v in residues]
    return [mask for mask, value in enumerate(residues) if value == 0]


def canonical(c, p):
    return min(tuple(sorted(k * x % p for x in c)) for k in range(1, p))


def admissible_orbits(p, size):
    return sorted({canonical(c, p)
                   for c in combinations_with_replacement(range(1, p), size)
                   if sum(c) % p == 0})


def create_nonexistence_certificate(p, size):
    records = []
    for c in admissible_orbits(p, size):
        rows = [[mask >> j & 1 for j in range(size)]
                for mask in zero_sum_masks(c, p)]
        vector, rank = rational_nullvector(rows, size)
        assert vector is not None, (p, c)
        records.append({"c": c, "integer_nullvector": vector,
                        "rational_rank": rank})
    return {"prime": p, "size": size, "records": records}


def verify_nonexistence_certificate(certificate):
    p, size = certificate["prime"], certificate["size"]
    expected = admissible_orbits(p, size)
    records = certificate["records"]
    assert [tuple(r["c"]) for r in records] == expected
    for record in records:
        c, z = record["c"], record["integer_nullvector"]
        assert len(z) == size and any(z)
        assert all(type(x) is int for x in z)
        # This check does not use a rank routine or the claimed rank field.
        for mask in zero_sum_masks(c, p):
            assert sum(z[j] for j in range(size) if mask >> j & 1) == 0
    return {"prime": p, "size": size, "projective_orbits": len(records),
            "all_integer_annihilators_valid": True}


SMALL = {
    7: {"c": [1, 1, 1, 1, 3, 3, 4], "B": [
        [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 1],
        [1, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 0],
        [0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 0]]},
    11: {"c": [1, 1, 1, 1, 3, 4, 4, 7], "B": [
        [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0, 1],
        [0, 0, 1, 1, 0, 0, 1], [0, 1, 0, 1, 0, 0, 1],
        [1, 0, 0, 1, 0, 0, 1], [1, 1, 1, 0, 1, 1, 0],
        [0, 0, 0, 1, 1, 1, 0]]},
    13: {"c": [1, 1, 1, 2, 3, 5, 5, 8], "B": [
        [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0, 1],
        [0, 0, 1, 1, 0, 0, 1], [1, 1, 0, 1, 0, 0, 1],
        [1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1, 0],
        [0, 0, 0, 1, 1, 1, 0]]},
    17: {"c": [1, 1, 2, 4, 4, 6, 7, 9], "B": [
        [1, 0, 0, 0, 0, 1, 1], [1, 1, 1, 1, 1, 0, 0],
        [0, 1, 0, 0, 1, 0, 1], [0, 1, 1, 1, 0, 1, 0],
        [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0],
        [0, 0, 0, 1, 1, 1, 0]]},
}


def verify_small_examples():
    results = []
    for p, item in SMALL.items():
        B, c = item["B"], item["c"]
        M = [[1] * len(c)] + [[0] + row for row in B]
        value = determinant(M)
        assert abs(value) == p
        assert all(0 < x < p for x in c)
        syndrome = [sum(x * y for x, y in zip(row, c)) for row in M]
        assert all(x % p == 0 for x in syndrome)
        # A square integer matrix of prime determinant has cyclic quotient C_p.
        results.append({"p": p, "support_size": len(c),
                        "determinant": value, "integer_syndrome": syndrome})
    return results


def positive_detector(q):
    """An augmented square Boolean matrix with cyclic row quotient C_q."""
    r = (q - 1).bit_length()
    a = [1] + [1 << i for i in range(r)]
    t, size = len(a), 2 * len(a)
    rows = []
    # Interleaved coordinate order x_0,y_0,x_1,y_1,... .
    for i in range(t):
        row = [0] * size
        row[2 * i] = row[2 * i + 1] = 1
        rows.append(row)
    for i in range(1, t):
        row = [0] * size
        for j in range(i):
            row[2 * j] = 1
        row[2 * i + 1] = 1
        rows.append(row)
    remaining, selected = q, []
    for i in range(t - 1, -1, -1):
        if a[i] <= remaining:
            selected.append(i)
            remaining -= a[i]
    assert remaining == 0
    row = [0] * size
    for i in selected:
        row[2 * i] = 1
    rows.append(row)
    # Replace the first pair row by the sum of all pair rows.
    rows[0] = [1] * size
    kernel = [v for x in a for v in (x, -x)]
    assert len(rows) == size
    return rows, a, kernel


def verify_positive_detectors():
    moduli = list(range(2, 33)) + [63, 127, 257, 1001, 65537]
    result = []
    for q in moduli:
        M, a, c = positive_detector(q)
        value = determinant(M)
        assert abs(value) == q
        assert all(x % q for x in c)
        assert all(sum(x * y for x, y in zip(row, c)) % q == 0 for row in M)
        assert all(x in (0, 1) for row in M for x in row)
        result.append({"q": q, "support_size": len(M),
                       "determinant": value, "a": a})
    # Direct spatial moments, independent of Fourier/kernel evaluation.
    spatial = []
    for q in (2, 3):
        M, a, c = positive_detector(q)
        s = len(M)
        total = 0
        for coordinates in product(range(q), repeat=s):
            term = 1
            for j in range(s):
                value = sum(coordinates[i] * M[i][j] for i in range(s)) % q
                term *= q - 1 if value == 0 else -1
            total += term
        assert Fraction(total, q ** s) == q - 1
        spatial.append({"q": q, "configurations": q ** s,
                        "exact_moment": str(Fraction(total, q ** s))})
    return result, spatial


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    folder = ROOT / "data"
    folder.mkdir(parents=True, exist_ok=True)
    negative = []
    for p in (11, 13):
        path = folder / f"no_seven_vertex_torsion_mod_{p}.json"
        if args.regenerate or not path.exists():
            certificate = create_nonexistence_certificate(p, 7)
            path.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
        certificate = json.loads(path.read_text())
        negative.append(verify_nonexistence_certificate(certificate))
    positive, spatial = verify_positive_detectors()
    report = {"status": "all exact checks passed", "small_prime_certificates":
              verify_small_examples(), "nonexistence_certificates": negative,
              "positive_detectors": positive, "direct_spatial_moments": spatial}
    (folder / "torsion_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    (folder / "small_prime_matrices.json").write_text(json.dumps(SMALL, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "small_primes": list(SMALL),
                      "nonexistence": negative, "positive_moduli": len(positive),
                      "spatial_checks": spatial}, indent=2))


if __name__ == "__main__":
    main()
