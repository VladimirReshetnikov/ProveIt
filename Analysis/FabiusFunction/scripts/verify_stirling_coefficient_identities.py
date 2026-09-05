"""Exact finite regressions for the Stirling/Bell coefficient identities.

This standard-library script is neither a mathematical proof nor Lean validation.
It compares independently evaluated recurrences and finite sums using integers
and fractions only. No floating-point arithmetic or external packages are used.
"""

from collections.abc import Iterator
from fractions import Fraction
from functools import cache
from math import comb, factorial, prod


@cache
def stirling_second(n: int, k: int) -> int:
    """Second-kind Stirling numbers from their block recurrence."""
    if n == 0:
        return int(k == 0)
    if k == 0 or k > n:
        return 0
    return k * stirling_second(n - 1, k) + stirling_second(n - 1, k - 1)


def weak_compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    """Enumerate all nonnegative tuples of the prescribed length and sum."""
    if length == 0:
        if total == 0:
            yield ()
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, length - 1):
            yield (first, *tail)


@cache
def complete_bell(n: int, weights: tuple[Fraction, ...]) -> Fraction:
    """Complete exponential Bell polynomial by the distinguished-block recurrence."""
    if n == 0:
        return Fraction(1)
    return sum(
        (comb(n - 1, j - 1) * weights[j - 1] * complete_bell(n - j, weights)
         for j in range(1, n + 1)),
        Fraction(0),
    )


@cache
def partial_bell(n: int, k: int, weights: tuple[Fraction, ...]) -> Fraction:
    """Partial exponential Bell polynomial, independent of the near-diagonal formula."""
    if n == 0:
        return Fraction(int(k == 0))
    if k == 0 or k > n:
        return Fraction(0)
    return sum(
        (comb(n - 1, j - 1) * weights[j - 1]
         * partial_bell(n - j, k - 1, weights)
         for j in range(1, n - k + 2)),
        Fraction(0),
    )


def check_equal(label: str, expected: int | Fraction, actual: int | Fraction) -> None:
    """Fail with the exact inputs and values, including when Python runs with -O."""
    if expected != actual:
        raise AssertionError(f"{label}: expected {expected}, got {actual}")


def check_reverse_rows() -> int:
    """Compare both summation ranges, including n < k and the trivial k = 0 case."""
    count = 0
    for n in range(15):
        for k in range(17):
            def term(j: int) -> int:
                return ((-1) ** j * factorial(j - 2) * comb(k + j - 1, j)
                        * stirling_second(n, k + j - 1))

            expected = (n - k) * stirling_second(n, k)
            uniform = sum(term(j) for j in range(2, n + 1))
            truncated = sum(term(j) for j in range(2, min(n, n - k + 1) + 1))
            check_equal(f"reverse row uniform n={n}, k={k}", expected, uniform)
            check_equal(f"reverse row truncated n={n}, k={k}", expected, truncated)
            count += 1
    return count


def check_stirling_columns() -> tuple[int, int]:
    """Check explicit tuples and factorially weighted power sums separately."""
    count = 0
    tuple_count = 0
    for k in range(7):
        weights = tuple(
            Fraction(factorial(m - 1) * sum(j ** m for j in range(1, k + 1)))
            for m in range(1, 7)
        )
        for r in range(7):
            homogeneous = 0
            for exponents in weak_compositions(r, k):
                homogeneous += prod((i + 1) ** c for i, c in enumerate(exponents))
                tuple_count += 1
            expected = stirling_second(k + r, k)
            check_equal(f"weak compositions k={k}, r={r}", expected, homogeneous)
            check_equal(f"Bell power sums k={k}, r={r}",
                        factorial(r) * expected, complete_bell(r, weights))
            count += 1
    return count, tuple_count


def check_near_diagonals() -> tuple[int, int, int]:
    """Check eq:bell-near-diagonal with its corrected upper bound min(2a, n)."""
    max_n = 12
    families = {
        "unit": tuple(Fraction(1) for j in range(1, max_n + 1)),
        "factorial": tuple(Fraction(factorial(j)) for j in range(1, max_n + 1)),
        "alternating integer": tuple(Fraction((-1) ** j * (j + 1))
                                     for j in range(1, max_n + 1)),
        "rational": tuple(Fraction((-1) ** (j - 1), j + 1)
                          for j in range(1, max_n + 1)),
        "zero singleton": tuple(Fraction(0 if j == 1 else j)
                                for j in range(1, max_n + 1)),
        "sparse even": tuple(Fraction(1, j) if j % 2 == 0 else Fraction(0)
                             for j in range(1, max_n + 1)),
        "zero": tuple(Fraction(0) for j in range(1, max_n + 1)),
    }
    count = zero_singleton_count = shortened_range_count = 0
    for name, weights in families.items():
        for n in range(2, max_n + 1):
            for a in range(1, n):
                shifted = tuple(weights[q] / (q + 1) for q in range(1, a + 1))
                expected = partial_bell(n, n - a, weights)
                actual = sum(
                    (Fraction(factorial(j), factorial(a)) * comb(n, j)
                     * weights[0] ** (n - j) * partial_bell(a, j - a, shifted)
                     for j in range(a + 1, min(2 * a, n) + 1)),
                    Fraction(0),
                )
                check_equal(f"near diagonal {name}, n={n}, a={a}", expected, actual)
                count += 1
                zero_singleton_count += int(weights[0] == 0)
                shortened_range_count += int(n < 2 * a)
    return count, zero_singleton_count, shortened_range_count


def main() -> None:
    rows = check_reverse_rows()
    columns, tuples = check_stirling_columns()
    diagonals, zero_singletons, shortened = check_near_diagonals()
    print(f"PASS reverse rows: {rows} cases, both uniform and truncated ranges")
    print(f"PASS weak compositions: {columns} cases, {tuples} tuples evaluated")
    print(f"PASS Bell power sums: {columns} cases")
    print(f"PASS near diagonals: {diagonals} cases across 7 weight families")
    print(f"  Includes {zero_singletons} cases with x1=0 and {shortened} with n<2a")
    print("Exact finite regression only; not a proof or Lean compilation result.")


if __name__ == "__main__":
    main()
