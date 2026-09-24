#!/usr/bin/env python3
"""Exact checks for the even-shift middle-binomial Hankel identity.

Python 3.10+; standard library only. Polynomials are tuples of integer
coefficients in ascending degree. No floating-point calculations are used.
These finite checks are reproducibility aids, not a proof of the theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial, prod
from pathlib import Path
import json
import platform
import time
from typing import Iterator

Poly = tuple[int, ...]
ZERO: Poly = (0,)
ONE: Poly = (1,)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def trim(p: list[int] | tuple[int, ...]) -> Poly:
    a = list(p)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a) if a else ZERO


def add(p: Poly, q: Poly) -> Poly:
    a = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        a[i] += c
    for i, c in enumerate(q):
        a[i] += c
    return trim(a)


def scale(p: Poly, c: int) -> Poly:
    return trim([c * a for a in p])


def sub(p: Poly, q: Poly) -> Poly:
    return add(p, scale(q, -1))


def mul(p: Poly, q: Poly) -> Poly:
    if p == ZERO or q == ZERO:
        return ZERO
    a = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            a[i + j] += x * y
    return trim(a)


def shift(p: Poly, r: int) -> Poly:
    require(r >= 0, "negative polynomial shift")
    return (0,) * r + p if p != ZERO else ZERO


def divide_exact(p: Poly, q: Poly) -> Poly:
    """Exact division in Z[t], with explicit remainder/integrality checks."""
    require(q != ZERO, "division by the zero polynomial")
    if p == ZERO:
        return ZERO
    require(len(p) >= len(q), "nonzero remainder in polynomial division")
    r = list(p)
    quotient = [0] * (len(p) - len(q) + 1)
    while len(r) >= len(q) and any(r):
        degree = len(r) - len(q)
        coefficient, residue = divmod(r[-1], q[-1])
        require(residue == 0, "nonintegral exact-division coefficient")
        quotient[degree] += coefficient
        for j, a in enumerate(q):
            r[degree + j] -= coefficient * a
        while r and r[-1] == 0:
            r.pop()
    require(not any(r), "nonzero remainder in exact division")
    return trim(quotient)


def determinant(matrix: list[list[Poly]]) -> Poly:
    """Fraction-free Bareiss determinant over Z[t], with row pivoting."""
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "nonsquare matrix")
    if n == 0:
        return ONE
    a = [list(row) for row in matrix]
    sign = 1
    previous = ONE
    for r in range(n - 1):
        if a[r][r] == ZERO:
            pivot_row = next((s for s in range(r + 1, n)
                              if a[s][r] != ZERO), None)
            if pivot_row is None:
                return ZERO
            a[r], a[pivot_row] = a[pivot_row], a[r]
            sign *= -1
        pivot = a[r][r]
        for i in range(r + 1, n):
            for j in range(r + 1, n):
                numerator = sub(mul(pivot, a[i][j]),
                                mul(a[i][r], a[r][j]))
                a[i][j] = divide_exact(numerator, previous)
        for i in range(r + 1, n):
            a[i][r] = ZERO
        previous = pivot
    return scale(a[-1][-1], sign)


def leibniz_determinant(matrix: list[list[Poly]]) -> Poly:
    """Independent signed-permutation determinant, only for small matrices."""
    n = len(matrix)
    result = ZERO
    for sigma in permutations(range(n)):
        inversions = sum(sigma[i] > sigma[j]
                         for i in range(n) for j in range(i + 1, n))
        term = ONE
        for i in range(n):
            term = mul(term, matrix[i][sigma[i]])
        result = add(result, scale(term, (-1)**inversions))
    return result


def moment(m: int) -> Poly:
    return tuple(comb(m // 2, j) * comb((m + 1) // 2, j)
                 for j in range(m // 2 + 1))


def hankel(k: int, n: int) -> Poly:
    raw = determinant([[moment(2 * k + i + j) for j in range(n)]
                       for i in range(n)])
    return divide_exact(raw, shift(ONE, n * n // 4))


def elementary(k: int, r: int) -> Poly:
    """e_r evaluated at k copies of 1 and k copies of t."""
    if not 0 <= r <= 2 * k:
        return ZERO
    return trim([comb(k, a) * comb(k, r - a)
                 if 0 <= r - a <= k else 0 for a in range(k + 1)])


def toeplitz(k: int, n: int) -> Poly:
    return determinant([[elementary(k, k + i - j) for j in range(n)]
                        for i in range(n)])


def complete(k: int, r: int) -> Poly:
    """h_r evaluated at the same repeated-variable alphabet."""
    if r < 0:
        return ZERO
    if k == 0:
        return ONE if r == 0 else ZERO
    return tuple(comb(k + a - 1, a) * comb(k + r - a - 1, r - a)
                 for a in range(r + 1))


def jacobi_trudi(k: int, n: int) -> Poly:
    return determinant([[complete(k, n - i + j) for j in range(k)]
                        for i in range(k)])


def partitions_in_box(k: int, n: int) -> Iterator[tuple[int, ...]]:
    if k == 0:
        yield ()
    else:
        for first in range(n + 1):
            for rest in partitions_in_box(k - 1, first):
                yield (first,) + rest


def weyl_dimension(lam: tuple[int, ...]) -> int:
    k = len(lam)
    numerator = prod(lam[a] - lam[b] + b - a
                     for a in range(k) for b in range(a + 1, k))
    denominator = prod(b - a for a in range(k)
                       for b in range(a + 1, k))
    q, r = divmod(numerator, denominator)
    require(r == 0 and q > 0, "invalid Weyl dimension")
    return q


def partition_sum(k: int, n: int) -> Poly:
    p = [0] * (k * n + 1)
    for lam in partitions_in_box(k, n):
        d = weyl_dimension(lam)
        p[sum(lam)] += d * d
    return trim(p)


def vandermonde(values: tuple[int, ...]) -> int:
    return prod(values[b] - values[a]
                for a in range(len(values))
                for b in range(a + 1, len(values)))


def numerator_blocks(k: int, n: int) -> list[Poly]:
    require(k >= 1, "numerator formula is stated for k >= 1")
    blocks = [[0] * (2 * j * (k - j) + 1) for j in range(k + 1)]
    full = tuple(range(2 * k))
    eps = tuple(a if a < k else n + a for a in full)
    factorial_product = prod(factorial(a) for a in range(k))
    for s in combinations(full, k):
        complement = tuple(a for a in full if a not in s)
        j = sum(a >= k for a in s)
        delta = sum(s) - k * (k - 1) // 2 - j * j
        require(0 <= delta <= 2 * j * (k - j), "delta outside bounds")
        numerator = (vandermonde(tuple(eps[a] for a in s)) *
                     vandermonde(tuple(eps[a] for a in complement)))
        weight, rem = divmod(numerator, factorial_product**2)
        require(rem == 0 and weight > 0, "nonintegral or nonpositive weight")
        blocks[j][delta] += (-1)**delta * weight
    result = [trim(p) for p in blocks]
    for j, p in enumerate(result):
        degree = 2 * j * (k - j)
        require(len(p) == degree + 1, "wrong exact numerator-block degree")
        require(result[k - j] == tuple(reversed(p)), "block reciprocity failed")
    return result


def reconstructed(k: int, n: int, blocks: list[Poly]) -> Poly:
    numerator = ZERO
    for j, p in enumerate(blocks):
        numerator = add(numerator, shift(scale(p, (-1)**j), j * (n + j)))
    denominator = tuple((-1)**r * comb(k * k, r)
                        for r in range(k * k + 1))
    return divide_exact(numerator, denominator)


def rectangular_dimension(k: int, n: int) -> int:
    value = Fraction(1)
    for i in range(1, k + 1):
        for j in range(1, k + 1):
            value *= Fraction(n + i + j - 1, i + j - 1)
    require(value.denominator == 1, "nonintegral rectangular dimension")
    return value.numerator


def run(max_k: int, max_n: int, output_dir: Path) -> dict:
    start = time.perf_counter()
    all_polynomials = {}
    sample_blocks = {}
    cases = 0
    determinant_comparisons = 0
    numerator_comparisons = 0
    leibniz_comparisons = 0
    previous_by_k: dict[int, Poly] = {}
    for k in range(max_k + 1):
        for n in range(max_n + 1):
            label = f"k={k},n={n}"
            p = partition_sum(k, n)
            for name, computed in (("Hankel", hankel(k, n)),
                                   ("Toeplitz", toeplitz(k, n)),
                                   ("Jacobi-Trudi", jacobi_trudi(k, n))):
                require(computed == p, f"{name} disagreement at {label}")
                determinant_comparisons += 1
            if n <= 4:
                raw_matrix = [[moment(2 * k + i + j) for j in range(n)]
                              for i in range(n)]
                raw_leibniz = leibniz_determinant(raw_matrix)
                require(raw_leibniz == shift(p, n * n // 4),
                        f"Leibniz audit failed at {label}")
                leibniz_comparisons += 1
            require(len(p) == k * n + 1, f"degree failed at {label}")
            require(all(c > 0 for c in p), f"positivity failed at {label}")
            require(p == tuple(reversed(p)), f"palindromicity failed at {label}")
            require(all(p[r] >= p[r - 1]
                        for r in range(1, (len(p) - 1) // 2 + 1)),
                    f"unimodality failed at {label}")
            require(sum(p) == rectangular_dimension(k, n),
                    f"t=1 dimension failed at {label}")
            if k >= 1:
                require(all(p[r] == comb(k * k + r - 1, r)
                            for r in range(n + 1)),
                        f"stable edge failed at {label}")
                blocks = numerator_blocks(k, n)
                require(reconstructed(k, n, blocks) == p,
                        f"numerator reconstruction failed at {label}")
                numerator_comparisons += 1
                if k <= 4 and n in (0, 1, 2, 3, max_n):
                    sample_blocks[label] = blocks
            if n > 0:
                old = previous_by_k[k]
                require(all(p[r] >= c for r, c in enumerate(old)),
                        f"coefficient monotonicity in n failed at {label}")
            previous_by_k[k] = p
            all_polynomials[label] = p
            cases += 1
    output_dir.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "PASS",
        "scope": "finite exact-arithmetic verification, not a formal proof",
        "max_k": max_k,
        "max_n": max_n,
        "parameter_pairs": cases,
        "independent_determinant_comparisons": determinant_comparisons,
        "numerator_reconstructions": numerator_comparisons,
        "signed_permutation_audits": leibniz_comparisons,
        "methods": ["raw shifted Hankel + exact normalization",
                    "elementary-symmetric Toeplitz determinant",
                    "complete-symmetric Jacobi-Trudi determinant",
                    "positive rectangular partition sum",
                    "confluent-alternant numerator expansion (k>=1)"],
        "additional_checks": ["degree", "strict positivity of each coefficient",
                              "palindromicity", "weak unimodality",
                              "Weyl dimension at t=1", "stable leading coefficients",
                              "coefficient monotonicity in n", "numerator block degrees",
                              "numerator block reciprocity", "integer exact divisions"],
        "disagreements": 0,
        "python_version": platform.python_version(),
        "elapsed_seconds": round(time.perf_counter() - start, 3)
    }
    (output_dir / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    (output_dir / "polynomials.json").write_text(json.dumps(all_polynomials, indent=2) + "\n")
    (output_dir / "numerator_blocks.json").write_text(json.dumps(sample_blocks, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=6)
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent / "results")
    args = parser.parse_args()
    if args.max_k < 0 or args.max_n < 0:
        parser.error("bounds must be nonnegative")
    print(json.dumps(run(args.max_k, args.max_n, args.output_dir), indent=2))


if __name__ == "__main__":
    main()
