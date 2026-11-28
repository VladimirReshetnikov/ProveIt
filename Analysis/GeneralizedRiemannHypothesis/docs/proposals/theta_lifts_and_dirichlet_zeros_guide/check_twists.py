"""Finite arithmetic examples from the chapter on quadratic-twist selection."""

from collections import Counter
from fractions import Fraction
from math import exp, fsum, isclose, isqrt, pi, sqrt


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def odd_squarefree_part(n):
    """Return the r in n = 2**a * r * h**2 with r odd and squarefree."""
    n = odd_part(n)
    factor = 3
    while factor * factor <= n:
        while n % (factor * factor) == 0:
            n //= factor * factor
        factor += 2
    return n


def jacobi(a, modulus):
    """Jacobi symbol for odd positive modulus."""
    assert modulus > 0 and modulus % 2 == 1
    a %= modulus
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if modulus % 8 in (3, 5):
                sign = -sign
        if a % 4 == modulus % 4 == 3:
            sign = -sign
        a, modulus = modulus % a, a
    return sign if modulus == 1 else 0


def character_correlation(n, m, length):
    return sum(jacobi(-v, odd_part(n * m)) for v in range(1, length + 1))


def theta7(u):
    """Odd Gaussian sum for the quadratic character modulo 7, truncated at 100."""
    return sqrt(u) * fsum(
        jacobi(n, 7) * (n * u) * exp(-pi * (n * u) ** 2)
        for n in range(1, 101)
    )


def main():
    assert character_correlation(12, 27, 12) == 8
    assert character_correlation(12, 2, 12) == 0

    # Verify the indexing bijection in the summability proof on a finite box.
    limit = 90
    groups = Counter(odd_squarefree_part(n) for n in range(1, limit + 1))
    by_squarefree_part = sum(size**2 for size in groups.values())
    by_square_test = sum(
        isqrt(odd_part(n * m)) ** 2 == odd_part(n * m)
        for n in range(1, limit + 1) for m in range(1, limit + 1)
    )
    assert by_squarefree_part == by_square_test

    # These floating-point checks illustrate the exact Poisson identity.
    value = abs(theta7(1))
    assert isclose(value, 0.043220892946908, abs_tol=1e-14)
    assert isclose(value, abs(theta7(1 / 7)), abs_tol=1e-14)
    assert isclose(abs(theta7(0.5)), abs(theta7(2 / 7)), abs_tol=1e-14)

    beta = Fraction(3, 4)
    delta = (beta - Fraction(1, 2)) / 9
    assert delta == Fraction(1, 36)
    exponent_T = (2 + delta) - 2 * delta
    assert exponent_T / 2 == Fraction(71, 72)
    print(f"Kernel sums: 8 and 0. Square-pair count at length 90: {by_square_test}.")
    print(f"Numerical fold for conductor 7: {value:.12f}. Bad-prime exponent: 71/72.")


if __name__ == "__main__":
    main()
