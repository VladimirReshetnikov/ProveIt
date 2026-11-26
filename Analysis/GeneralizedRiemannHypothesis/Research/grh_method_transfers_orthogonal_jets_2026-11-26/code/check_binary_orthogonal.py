#!/usr/bin/env python3
"""Exact finite checks for binary orthogonal principal-submatrix bounds.

Enumerates O_n(F_2) = {Q : Q^T Q = I} by its orthonormal columns,
without enumerating all GL_n matrices.  Every principal subset is tested
for n <= 6.  It also checks the canonical symplectic quotient images and
fibers, and independently counts independent symplectic frames by Gram
matrix.  All decisions use integers or fractions; no floating point.

These finite checks verify definitions, small cases, and orbit-count
inputs.  The universal tail estimate is proved in the accompanying
report, not established by finite enumeration.  The resulting tail bound
is numerically vacuous for n <= 6; the output records this explicitly.

Python 3.10+, standard library only. Run without -O.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from math import prod
from pathlib import Path


def parity(x: int) -> int:
    return x.bit_count() & 1


def rank(vectors: tuple[int, ...] | list[int]) -> int:
    """Column rank over F_2; integers encode binary columns."""
    basis: dict[int, int] = {}
    for vector in vectors:
        x = vector
        while x:
            pivot = x.bit_length() - 1
            if pivot in basis:
                x ^= basis[pivot]
            else:
                basis[pivot] = x
                break
    return len(basis)


def orthogonal_matrices(n: int):
    """Each yielded tuple is the n columns of one Q with Q^T Q = I."""
    candidates = tuple(x for x in range(1, 1 << n) if parity(x))

    def recurse(columns: tuple[int, ...], available: tuple[int, ...]):
        if len(columns) == n:
            yield columns
            return
        for v in available:
            next_available = tuple(w for w in available if not parity(v & w))
            yield from recurse(columns + (v,), next_available)

    yield from recurse((), candidates)


def apply_matrix(columns: tuple[int, ...], vector: int) -> int:
    result = 0
    while vector:
        bit = vector & -vector
        result ^= columns[bit.bit_length() - 1]
        vector ^= bit
    return result


def symplectic_group_order(dimension: int) -> int:
    assert dimension >= 0 and dimension % 2 == 0
    m = dimension // 2
    return (1 << (m * m)) * prod((1 << (2 * i)) - 1 for i in range(1, m + 1))


def canonical_symplectic_image(columns: tuple[int, ...]) -> tuple[int, ...]:
    """Canonical characteristic-two reduction, in an explicit even basis.

    Odd n: c=(1,...,1) has norm 1 and c^perp is symplectic.
    Even n: c^perp/<c> is symplectic; choose representatives in the
    even-weight subspace supported on the first n-1 coordinates.
    In either case the chosen Gram matrix has zero diagonal and all
    off-diagonal entries equal to one; its dimension is even.
    """
    n = len(columns)
    c = (1 << n) - 1
    assert apply_matrix(columns, c) == c
    if n % 2:
        dimension = n - 1
        basis = tuple((1 << i) | (1 << (n - 1)) for i in range(dimension))
        low_mask = (1 << dimension) - 1
        images = []
        for vector in basis:
            image = apply_matrix(columns, vector)
            assert parity(image) == 0
            images.append(image & low_mask)
        return tuple(images)
    dimension = n - 2
    basis = tuple((1 << i) | (1 << (n - 2)) for i in range(dimension))
    low_mask = (1 << dimension) - 1
    images = []
    for vector in basis:
        image = apply_matrix(columns, vector)
        assert parity(image) == 0
        if image & (1 << (n - 1)):
            image ^= c
        assert image >> (n - 1) == 0 and parity(image) == 0
        images.append(image & low_mask)
    return tuple(images)


def fraction_json(x: Fraction) -> dict[str, int]:
    return {"numerator": x.numerator, "denominator": x.denominator}


def check_orthogonal_groups(max_n: int) -> list[dict]:
    expected_orders = {1: 1, 2: 2, 3: 6, 4: 48, 5: 720, 6: 23040}
    results = []
    for n in range(1, max_n + 1):
        subsets = [(mask, tuple(i for i in range(n) if mask >> i & 1))
                   for mask in range(1 << n)]
        maxima = Counter()
        by_size = [Counter() for _ in range(n + 1)]
        quotient_fibers = Counter()
        max_witness: tuple[int, ...] = ()
        max_seen = -1
        total = 0
        for columns in orthogonal_matrices(n):
            total += 1
            assert rank(columns) == n
            assert all(parity(columns[i] & columns[j]) == (i == j)
                       for i in range(n) for j in range(n))
            largest = 0
            for mask, indices in subsets:
                k = len(indices)
                deficiency = k - rank([columns[i] & mask for i in indices])
                assert 0 <= deficiency <= min(k, n - k)
                by_size[k][deficiency] += 1
                largest = max(largest, deficiency)
            maxima[largest] += 1
            if largest > max_seen:
                max_seen, max_witness = largest, columns
            image = canonical_symplectic_image(columns)
            assert rank(image) == len(image)
            # The explicit basis has Gram I+all-ones, which is alternating
            # and nondegenerate in every even dimension.
            for i, vi in enumerate(image):
                for j, vj in enumerate(image):
                    gram = parity(vi & vj) ^ (parity(vi) & parity(vj))
                    assert gram == (i != j)
            quotient_fibers[image] += 1
        assert total == expected_orders[n]
        assert sum(maxima.values()) == total
        dimension = n - 1 if n % 2 else n - 2
        assert len(quotient_fibers) == symplectic_group_order(dimension)
        assert len(set(quotient_fibers.values())) == 1
        fiber = next(iter(quotient_fibers.values()))
        assert fiber == (1 if n % 2 else (1 << (n - 1)))
        tails = []
        for r in range(1, n + 1):
            observed = Fraction(sum(count for d, count in maxima.items() if d >= r), total)
            exponent = n - r * (r - 1) // 2
            raw_bound = Fraction(6) * (Fraction(2) ** exponent)
            bound = min(Fraction(1), raw_bound) if r <= n // 2 else Fraction(0)
            assert observed <= bound
            tails.append({"r": r, "observed": fraction_json(observed),
                          "bound": fraction_json(bound),
                          "nontrivial_exponential_bound": r <= n // 2 and raw_bound < 1})
        item = {
            "n": n, "group_order": total,
            "maximum_nullity_histogram": dict(sorted(maxima.items())),
            "submatrix_nullity_counts_by_size": [dict(sorted(c.items())) for c in by_size],
            "all_principal_subsets_checked": total * (1 << n),
            "largest_nullity_seen": max_seen,
            "witness_columns_as_bitmasks": list(max_witness),
            "symplectic_image_dimension": dimension,
            "symplectic_image_order": len(quotient_fibers),
            "each_quotient_fiber_size": fiber,
            "tails": tails,
        }
        results.append(item)
        print(f"n={n}: {total} matrices, {total * (1 << n)} principal subsets; "
              f"max-nullity histogram {dict(sorted(maxima.items()))}", flush=True)
    return results


def symplectic_pair(x: int, y: int, dimension: int) -> int:
    """Standard block form with pairs (0,1),(2,3),... ."""
    total = 0
    for i in range(0, dimension, 2):
        total ^= ((x >> i & 1) & (y >> (i + 1) & 1))
        total ^= ((x >> (i + 1) & 1) & (y >> i & 1))
    return total


def check_symplectic_frame_counts() -> list[dict]:
    results = []
    for dimension in (2, 4, 6):
        for length in range(1, dimension // 2 + 1):
            counts = Counter()

            def recurse(frame: tuple[int, ...], span: frozenset[int], gram: int):
                if len(frame) == length:
                    counts[gram] += 1
                    return
                i = len(frame)
                offset = i * (i - 1) // 2
                for v in range(1, 1 << dimension):
                    if v in span:
                        continue
                    new_gram = gram
                    for j, w in enumerate(frame):
                        new_gram |= symplectic_pair(w, v, dimension) << (offset + j)
                    new_span = span | frozenset(w ^ v for w in span)
                    recurse(frame + (v,), new_span, new_gram)

            recurse((), frozenset({0}), 0)
            assert len(counts) == 1 << (length * (length - 1) // 2)
            total_expected = prod((1 << dimension) - (1 << i) for i in range(length))
            assert sum(counts.values()) == total_expected
            lower_product = prod((1 << (dimension - i)) - (1 << i)
                                 for i in range(length))
            exponent = dimension * length - length * (length - 1) // 2
            for count in counts.values():
                assert count >= lower_product
                assert 3 * count >= 2 * (1 << exponent)
            results.append({"dimension": dimension, "frame_length": length,
                            "counts_by_alternating_gram_bitmask": dict(sorted(counts.items())),
                            "number_of_independent_frames": total_expected,
                            "sequential_lower_bound": lower_product,
                            "minimum_gram_class_size": min(counts.values()),
                            "power_exponent": exponent,
                            "constant_lower_bound": "2/3"})
            print(f"symplectic dimension={dimension}, frame length={length}: "
                  f"{total_expected} independent frames, {len(counts)} Gram classes", flush=True)
    return results


def main() -> None:
    if not __debug__:
        raise SystemExit("Run with assertions enabled (do not use python -O).")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=6, choices=range(1, 7))
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "checks/binary_orthogonal_checks.json")
    args = parser.parse_args()
    orthogonal = check_orthogonal_groups(args.max_n)
    frames = check_symplectic_frame_counts()
    # Elementary product estimates used in the universal constant C<6.
    # prod_{j>=3}(1-2^-j) >= 1-sum_{j>=3}2^-j = 3/4.
    # prod_{j>=2}(1-4^-j) >= 1-sum_{j>=2}4^-j = 11/12.
    c_gl_lower = Fraction(1, 2) * Fraction(3, 4) * Fraction(3, 4)
    c_sp_lower = Fraction(3, 4) * Fraction(11, 12)
    assert c_gl_lower > Fraction(1, 4)
    assert c_sp_lower > Fraction(2, 3)
    assert 1 / (c_gl_lower * c_sp_lower) < 6
    output = {
        "status": "all exact assertions passed",
        "scope": "Exhaustive small-group and principal-submatrix enumeration; symplectic quotient fibers; independent frame Gram-class counts.",
        "limitation": "For n<=6 the nonzero exponential upper bound is vacuous; asymptotic theorem requires the report proof. No conclusion about a matching lower order is asserted.",
        "orthogonal": orthogonal,
        "symplectic_frames": frames,
        "constants": {"GL_product_lower_bound": fraction_json(c_gl_lower),
                      "Sp_product_lower_bound": fraction_json(c_sp_lower),
                      "reciprocal_product_upper_bound": fraction_json(1 / (c_gl_lower * c_sp_lower))},
        "total_matrices": sum(x["group_order"] for x in orthogonal),
        "total_principal_subsets": sum(x["all_principal_subsets_checked"] for x in orthogonal),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(f"All checks passed. Results: {args.output}")


if __name__ == "__main__":
    main()
