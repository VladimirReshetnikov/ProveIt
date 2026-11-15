"""Exact finite algorithms used in the logarithmic-integral PNT manuscript.

These are executable specifications and numerical sanity-check aids, not a
proof checker and not a substitute for an iPRA derivation. Python integers
stand for unbounded natural-number arithmetic. The theorem thresholds are
too large to materialize; compute their exponents or symbolic descriptions.
"""

from fractions import Fraction
from math import isqrt

C = 1 << 240
D = 2 * C
ANALYTIC_SCALE = 1 << 100


def bit_length(n: int) -> int:
    """Totalized binary length; the theorem uses only n >= 2."""
    return max(1, n.bit_length())


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d != 0 for d in range(2, isqrt(n) + 1))


def prime_count(n: int) -> int:
    return sum(is_prime(p) for p in range(2, n + 1))


def floor_log2_rat(u: Fraction) -> int:
    """Bounded search for e with 2**e <= u < 2**(e+1), for u >= 1."""
    if u < 1:
        raise ValueError("The logarithm specification requires u >= 1")
    # The numerator's binary length is a supplied finite search bound.
    candidates = range(u.numerator.bit_length() + 1)
    return max(e for e in candidates if (1 << e) * u.denominator <= u.numerator)


def atanh_sum(r: Fraction, terms: int) -> Fraction:
    """2 sum_{j<terms} ((r-1)/(r+1))^(2j+1)/(2j+1)."""
    z = (r - 1) / (r + 1)
    z2 = z * z
    power = z
    result = Fraction(0)
    for j in range(terms):
        result += 2 * power / (2 * j + 1)
        power *= z2
    return result


def log_lower(u: Fraction | int, precision: int) -> Fraction:
    """The manuscript's lambda(u, v), a rational lower bound for log u."""
    u = Fraction(u)
    e = floor_log2_rat(u)
    r = u / (1 << e)
    terms = precision + e + 2
    return e * atanh_sum(Fraction(2), terms) + atanh_sum(r, terms)


def log_interval(u: Fraction | int, precision: int) -> tuple[Fraction, Fraction]:
    u = Fraction(u)
    e = floor_log2_rat(u)
    terms = precision + e + 2
    lo = log_lower(u, precision)
    return lo, lo + Fraction(e + 1, 9**terms)


def li_approx(n: int, precision: int) -> Fraction:
    """Exact A(n,v) from the manuscript. Slow by design; no adaptive loops.

    There are (n-2)*2**(v+3) exact rational summands. Use small inputs for
    demonstration. The specification is totalized to zero for n < 2.
    """
    if n < 2:
        return Fraction(0)
    grid = 1 << (precision + 3)
    terms = (n - 2) * grid
    log_precision = precision + bit_length(n) + 6
    result = Fraction(0)
    for j in range(terms):
        t = Fraction(2 * grid + j, grid)
        result += 1 / log_lower(t, log_precision)
    return result / grid


def li_interval(n: int, precision: int) -> tuple[Fraction, Fraction]:
    a = li_approx(n, precision)
    return a - Fraction(1, 1 << precision), a


def threshold_exponent(m: int) -> int:
    """N(m) is 2**threshold_exponent(m); do not construct that integer."""
    return D * (m + 7) ** 10


def above_threshold(n: int, m: int) -> bool:
    """Exact comparison with N(m), without materializing N(m)."""
    return n > 0 and n.bit_length() > threshold_exponent(m)


def inverse_log_M(k: int) -> int:
    return 1 + 6400 * C * C * k * k + 48 * C


def expansion_constant(r: int) -> int:
    fac = 1
    for j in range(1, r + 1):
        fac *= j
    return 1 + fac * (1 + (1 << (r + 2)))


def cleared_matrix(n: int, m: int, v: int, a: Fraction) -> bool:
    """Exact integer matrix, independent of the theorem's antecedent.

    Passing tests on small n does not prove the PNT theorem. This function
    exists to make the target unambiguous.
    """
    b = bit_length(n)
    den = a.denominator
    z = abs(den * prime_count(n) - a.numerator)
    left = z * (1 << (m + v)) * b
    right = den * (n * (1 << v) + (1 << m) * b)
    return left <= right


def finite_abel(a: list[Fraction], b: list[Fraction]) -> tuple[Fraction, Fraction]:
    if len(a) != len(b):
        raise ValueError("The finite lists must have the same length")
    if not a:
        return Fraction(0), Fraction(0)
    cumulative = []
    acc = Fraction(0)
    for value in a:
        acc += value
        cumulative.append(acc)
    lhs = sum((x * y for x, y in zip(a, b)), Fraction(0))
    rhs = cumulative[-1] * b[-1]
    rhs += sum((cumulative[i] * (b[i] - b[i + 1])
                for i in range(len(a) - 1)), Fraction(0))
    return lhs, rhs


if __name__ == "__main__":
    import json
    print(json.dumps({
        "C": str(C),
        "D": str(D),
        "main_threshold": "2^(2^241 * (m+7)^10)",
        "threshold_at_m_0_exponent": str(threshold_exponent(0)),
        "prime_count_100": prime_count(100),
        "status": "Executable arithmetic specification; not a universal proof"
    }, indent=2))
