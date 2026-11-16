"""Exact, bounded arithmetic for an elementary effective Siegel subcase.

This is a reference implementation, not an iPRA proof checker.  The accompanying
paper proves the certificate theorem.  A successful certificate check supplies
all finite input needed by that theorem.  All algorithms have explicit finite
loop bounds and use integer or rational arithmetic only.

Polynomials are dense tuples of integer coefficients in ascending degree order.
The zero polynomial is ().  A Runge certificate is D^2*f = A^2 + R, where D > 0,
deg(A) >= 1, and 0 <= deg(R) < deg(A).  In particular, R must be nonzero.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from math import gcd
from typing import Iterable

Poly = tuple[int, ...]
Point = tuple[int, int]


class CertificateError(ValueError):
    """The supplied data do not satisfy this certificate theorem's hypotheses."""


def normalize(values: Iterable[int]) -> Poly:
    result = list(values)
    if any(type(value) is not int for value in result):
        raise TypeError("Polynomial coefficients must be integers.")
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def degree(poly: Poly) -> int:
    return len(normalize(poly)) - 1


def coefficient(poly: Poly, index: int) -> int:
    return poly[index] if 0 <= index < len(poly) else 0


def add(left: Poly, right: Poly) -> Poly:
    return normalize(
        coefficient(left, i) + coefficient(right, i)
        for i in range(max(len(left), len(right)))
    )


def scale(multiplier: int, poly: Poly) -> Poly:
    return normalize(multiplier * value for value in poly)


def multiply(left: Poly, right: Poly) -> Poly:
    if not left or not right:
        return ()
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return normalize(result)


def evaluate(poly: Poly, x: int) -> int:
    result = 0
    for coefficient_value in reversed(poly):
        result = result * x + coefficient_value
    return result


def isqrt_bounded(n: int) -> int:
    """Return floor(sqrt(n)) by a binary search with a prescribed loop count.

    The invariant is lo^2 <= n < hi^2.  Initially lo=0, hi=n+1.  Each step
    halves the interval, up to rounding, so bit_length(n)+1 steps suffice.
    bit_length itself is primitive recursive (a bounded count of powers of 2).
    This implementation avoids an unbounded search for a square root.
    """
    if n < 0:
        raise ValueError("Integer square root needs a nonnegative input.")
    lo, hi = 0, n + 1
    for _ in range(n.bit_length() + 1):
        middle = (lo + hi) // 2
        if middle * middle <= n:
            lo = middle
        else:
            hi = middle
    assert lo * lo <= n < (lo + 1) * (lo + 1)
    return lo


@dataclass(frozen=True)
class RungeCertificate:
    D: int
    A: Poly
    R: Poly

    def to_dict(self) -> dict:
        return asdict(self)


def check_certificate(f: Poly, certificate: RungeCertificate) -> bool:
    """Decide the finite algebraic certificate conditions, without search."""
    try:
        f = normalize(f)
        A, R = normalize(certificate.A), normalize(certificate.R)
        return (
            type(certificate.D) is int
            and certificate.D >= 1
            and degree(A) >= 1
            and 0 <= degree(R) < degree(A)
            and scale(certificate.D**2, f) == add(multiply(A, A), R)
        )
    except (TypeError, AttributeError):
        return False


def construct_certificate(f: Poly) -> RungeCertificate:
    """Complete the square at infinity for a square-leading even-degree f.

    A rational polynomial Q of half the degree is chosen top-down so that
    deg(f-Q^2) < deg(Q).  Clearing its denominators produces D, A=D*Q,
    R=D^2*f-A^2.  A zero remainder is rejected because the finiteness theorem
    explicitly requires R != 0.  Odd degree and nonsquare leading coefficients
    are outside this constructor's scope; rejection is not an infinitude claim.
    """
    f = normalize(f)
    n = degree(f)
    if n < 2 or n % 2:
        raise CertificateError("Expected a positive even degree of at least two.")
    leading = f[-1]
    if leading <= 0:
        raise CertificateError("Expected a positive square leading coefficient.")
    root = isqrt_bounded(leading)
    if root * root != leading:
        raise CertificateError("Leading coefficient is not an integer square.")

    m = n // 2
    q = [Fraction(0) for _ in range(m + 1)]
    q[m] = Fraction(root)
    for j in range(m - 1, -1, -1):
        exponent = m + j
        known = sum(
            (q[i] * q[exponent - i]
             for i in range(m + 1)
             if 0 <= exponent - i <= m),
            Fraction(0),
        )
        q[j] = (Fraction(f[exponent]) - known) / (2 * root)

    D = 1
    for value in q:
        D = D * value.denominator // gcd(D, value.denominator)
    A = normalize(int(D * value) for value in q)
    R = add(scale(D * D, f), scale(-1, multiply(A, A)))
    if not R:
        raise CertificateError("Zero remainder: f is a rational polynomial square.")
    certificate = RungeCertificate(D=D, A=A, R=R)
    assert check_certificate(f, certificate)
    return certificate


def coordinate_bounds(f: Poly, certificate: RungeCertificate) -> tuple[int, int]:
    """The proved complete rectangle is |x| <= H and |y| <= K."""
    if not check_certificate(f, certificate):
        raise CertificateError("Invalid Runge certificate.")
    A, R = normalize(certificate.A), normalize(certificate.R)
    H = sum(abs(value) for value in A[:-1]) + sum(abs(value) for value in R)
    K = evaluate(tuple(abs(value) for value in normalize(f)), H)
    return H, K


def enumerate_x_interval(f: Poly, H: int) -> list[Point]:
    """List exactly the integral solutions with |x| <= H, using bounded roots."""
    if H < 0:
        return []
    points: set[Point] = set()
    for x in range(-H, H + 1):
        value = evaluate(f, x)
        if value < 0:
            continue
        y = isqrt_bounded(value)
        if y * y == value:
            points.add((x, -y))
            points.add((x, y))
    return sorted(points)


def solve_with_certificate(f: Poly, certificate: RungeCertificate) -> list[Point]:
    H, _ = coordinate_bounds(f, certificate)
    return enumerate_x_interval(f, H)


def quartic_polynomial(a: int, b: int) -> Poly:
    return (b, 0, a, 0, 1)


def quartic_bounds(a: int, b: int) -> dict[str, int | bool]:
    """Use 4*x^2 <= |a^2-4*b|+1-2*a and 4*|y| <= |a^2-4*b|+1."""
    delta = a * a - 4 * b
    if delta == 0:
        raise CertificateError("The nonzero-delta hypothesis fails.")
    d = abs(delta)
    x_square_numerator = d + 1 - 2 * a
    empty = x_square_numerator < 0
    H = -1 if empty else isqrt_bounded(x_square_numerator // 4)
    return {
        "delta": delta,
        "four_x_squared_bound": x_square_numerator,
        "four_abs_y_bound": d + 1,
        "H": H,
        "K": (d + 1) // 4,
        "forced_empty": empty,
    }


def solve_quartic_by_divisors(a: int, b: int) -> list[Point]:
    """Exact signed-divisor algorithm for y^2=x^4+a*x^2+b, delta != 0.

    For u*v=delta, recover x^2=(u+v-2*a)/4 and y=(v-u)/4, checking the
    congruences and the square condition.  Every u is in [-|delta|, |delta|].
    """
    delta = a * a - 4 * b
    if delta == 0:
        raise CertificateError("The nonzero-delta hypothesis fails.")
    d = abs(delta)
    points: set[Point] = set()
    for u in range(-d, d + 1):
        if u == 0 or delta % u:
            continue
        v = delta // u
        x_square_numerator = u + v - 2 * a
        y_numerator = v - u
        if x_square_numerator < 0 or x_square_numerator % 4 or y_numerator % 4:
            continue
        x_squared = x_square_numerator // 4
        x = isqrt_bounded(x_squared)
        if x * x != x_squared:
            continue
        y = y_numerator // 4
        points.add((-x, y))
        points.add((x, y))
    return sorted(points)


def hyperelliptic_family(m: int) -> Poly:
    if m < 2:
        raise ValueError("The family here uses m >= 2.")
    coefficients = [0] * (2 * m + 1)
    coefficients[0] = coefficients[1] = coefficients[2 * m] = 1
    return tuple(coefficients)


if __name__ == "__main__":
    import json

    f = quartic_polynomial(7, 1)
    certificate = construct_certificate(f)
    print(json.dumps({
        "polynomial_ascending": f,
        "certificate": certificate.to_dict(),
        "bounds": coordinate_bounds(f, certificate),
        "points": solve_with_certificate(f, certificate),
        "sharp_quartic_bounds": quartic_bounds(7, 1),
    }, indent=2))
