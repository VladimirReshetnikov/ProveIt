"""Exact ballot-moment Hankel determinants and their product formulas.

Only Python's standard library is required (Python 3.9+).
All arithmetic is integral or rational. Coefficient arrays are in ascending
order. The product formula also defines the bilateral continuation in n.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, prod
from typing import List, Sequence, Tuple, Union

Rational = Union[int, Fraction]


def _nonnegative(name: str, value: int) -> None:
    if not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def sign_power(exponent: int) -> int:
    """Return (-1)**exponent as an integer, including negative exponents."""
    return -1 if exponent % 2 else 1


def admissible(k: int, n: int) -> Tuple[int, ...]:
    """The deletion indices giving parity-balanced Chebyshev minors."""
    if not isinstance(k, int) or k < 1 or not isinstance(n, int):
        raise ValueError("k must be a positive integer and n an integer")
    return tuple(range(0 if k % 2 == 0 else n % 2, k + 1, 2))


@lru_cache(maxsize=None)
def coefficient(k: int, n: int, a: int) -> int:
    """C_{k,a}(n); integer-valued, strictly positive for n >= 1.

    For negative n the same product supplies the polynomial continuation.
    An inadmissible a has coefficient zero.
    """
    allowed = admissible(k, n)
    if not isinstance(a, int):
        raise ValueError("a must be an integer")
    if a not in allowed:
        return 0
    degrees = [d for d in range(n - 1, n + k) if d != n + a - 1]
    even = [d // 2 for d in degrees if d % 2 == 0]
    odd = [d // 2 for d in degrees if d % 2]
    if len(even) != (k + 1) // 2 or len(odd) != k // 2:
        raise ArithmeticError("Unbalanced parity blocks")
    numerator = (
        prod((b - a) * (b + a + 1) for a, b in combinations(even, 2))
        * prod(m + 1 for m in odd)
        * prod((b - a) * (b + a + 2) for a, b in combinations(odd, 2))
    )
    denominator = (
        prod(factorial(2 * i) for i in range(len(even)))
        * prod(factorial(2 * i + 1) for i in range(len(odd)))
    )
    q, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError("The integer-valued product was not integral")
    return q


def rho_coefficients(k: int, n: int) -> List[int]:
    """Coefficients [constant, t, ..., t**floor(k/2)] of rho_k(n,t)."""
    if not isinstance(n, int) or n < 1:
        raise ValueError("rho_coefficients requires n >= 1")
    return [coefficient(k, n, a) for a in reversed(admissible(k, n))]


def delta(k: int, n: int, t: Rational = 1, u: Rational = 1) -> Fraction:
    """Evaluate the normalized determinant (or its bilateral continuation).

    For n >= 0 this is a polynomial evaluation, including at t=0.
    For n < 0, t must be nonzero. It is the exponential-polynomial
    continuation, not the determinant of a matrix of negative size.
    """
    admissible(k, n)  # Validate even at n=0.
    t, u = Fraction(t), Fraction(u)
    if n == 0:
        return Fraction(1)
    if n < 0 and t == 0:
        raise ValueError("The negative-index continuation requires t != 0")
    total = Fraction(0)
    for a in admissible(k, n):
        c = coefficient(k, n, a)
        if c:
            total += c * u**a * t**((k * n - a) // 2)
    return sign_power(k * n * (n - 1) // 2) * total


def delta_polynomial(k: int, n: int) -> List[int]:
    """Coefficients of delta_k(n,t), with u=1 and n >= 0."""
    _nonnegative("n", n)
    admissible(k, n)
    if n == 0:
        return [1]
    result = [0] * (k * n // 2 + 1)
    sign = sign_power(k * n * (n - 1) // 2)
    for a in admissible(k, n):
        result[(k * n - a) // 2] = sign * coefficient(k, n, a)
    return result


def moment(m: int, t: Rational = 1, u: Rational = 1) -> Fraction:
    """a_m(u,t), independently evaluated from its defining ballot sum."""
    _nonnegative("m", m)
    t, u = Fraction(t), Fraction(u)
    return sum(
        ((comb(m, h) - (comb(m, h - 1) if h else 0))
         * u**(m - 2 * h) * t**h for h in range(m // 2 + 1)),
        Fraction(0),
    )


def bareiss_determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Exact integer determinant by fraction-free elimination with pivoting."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("The matrix must be square")
    if any(not isinstance(v, int) for row in matrix for v in row):
        raise ValueError("Bareiss elimination expects integer entries")
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = pivot * a[i][j] - a[i][k] * a[k][j]
                q, remainder = divmod(value, previous)
                if remainder:
                    raise ArithmeticError("Non-exact Bareiss division")
                a[i][j] = q
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def direct_hankel(k: int, n: int, t: int = 1, u: int = 1) -> int:
    """Independent determinant of the defining moment matrix."""
    _nonnegative("k", k)
    _nonnegative("n", n)
    if not isinstance(t, int) or not isinstance(u, int):
        raise ValueError("The independent determinant requires integer weights")
    values = [int(moment(m, t, u)) for m in range(k + max(2 * n - 1, 0))]
    return bareiss_determinant(
        [[values[k + i + j] for j in range(n)] for i in range(n)]
    )


def adjacent_ratio(k: int, n: int, j: int) -> Fraction:
    """b_{j+1}/b_j, where b_j = C_{k,epsilon+2j}(n)."""
    admissible(k, n)
    r = k // 2
    if n < 1 or not 0 <= j < r:
        raise ValueError("Require n >= 1 and 0 <= j < floor(k/2)")
    if k % 2 == 0 and n % 2:
        return Fraction(
            (r - j) * (n + j) * (n + 2 * j + 2),
            (j + 1) * (n + r + j + 1) * (n + 2 * j),
        )
    L = n + n % 2
    return Fraction((r - j) * (L + j), (j + 1) * (L + r + j + 1))


def rho_coefficients_fast(k: int, n: int) -> List[int]:
    """One product evaluation, followed by exact adjacent-ratio updates."""
    if not isinstance(n, int) or n < 1:
        raise ValueError("rho_coefficients_fast requires n >= 1")
    aa = admissible(k, n)
    b = [coefficient(k, n, aa[0])]
    for j in range(k // 2):
        value = b[-1] * adjacent_ratio(k, n, j)
        if value.denominator != 1:
            raise ArithmeticError("A coefficient update was not integral")
        b.append(value.numerator)
    return list(reversed(b))


def leading_constant(k: int) -> Fraction:
    """K_k in C_{k,epsilon+2j}(n) ~ K_k binom(r,j) n**floor(k*k/4)."""
    admissible(k, 0)
    r = k // 2
    p = prod(factorial(i) for i in range(1, r))**2
    if k % 2:
        return Fraction(factorial(r) * p,
                        2**r * prod(factorial(i) for i in range(2 * r + 1)))
    return Fraction(p, 2**r * prod(factorial(i) for i in range(2 * r)))


def denominator(k: int, t: Rational = 1) -> List[Fraction]:
    """Coefficients in x of the prescribed generating-function denominator."""
    admissible(k, 0)
    r, t = k // 2, Fraction(t)
    if k % 2:
        power = r * r + r + 1
        q = [Fraction(0)] * (2 * power + 1)
        for j in range(power + 1):
            q[2 * j] = comb(power, j) * t**(k * j)
    else:
        power = r * r
        q = [Fraction(0)] * (2 * power + 2)
        for j in range(power + 1):
            c = comb(power, j) * (-t**(2 * r))**j
            q[2 * j] += c
            q[2 * j + 1] -= t**r * c
    return q


def numerator(k: int, t: Rational = 1) -> List[Fraction]:
    """Coefficients in x of A_k(x,t), computed by finite convolution."""
    q = denominator(k, t)
    degree = len(q) - 1 - k
    values = [delta(k, n, t) for n in range(degree + 1)]
    return [sum((q[j] * values[n - j] for j in range(min(n, len(q)-1)+1)),
                Fraction(0)) for n in range(degree + 1)]


if __name__ == "__main__":
    for k in range(1, 9):
        print(f"rho_{k}(10,t), ascending coefficients:", rho_coefficients(k, 10))
    print("delta_4(7; u=1,t=2) =", delta(4, 7, t=2))
    print("A_4(x,2), ascending coefficients:", numerator(4, t=2))
