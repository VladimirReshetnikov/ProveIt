"""Exact rational certificates for Gaussian multiple polylogarithms.

The mathematics is proved in the accompanying article.  This implementation
uses Hoelder convolution at 1/2 and rational Taylor coefficients; it does not
use numerical quadrature, floating-point arithmetic, or an MPL evaluator.

All errors returned here bound the complex modulus.  Thus the same error is
valid for each real coordinate separately.  An enclosure is evidence about
the value, not a proof of a proposed transcendental identity.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb


@dataclass(frozen=True)
class Gaussian:
    """An element of Q(i), represented by two exact rational numbers."""

    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "re", Q(self.re))
        object.__setattr__(self, "im", Q(self.im))

    def __add__(self, other):
        other = gaussian(other)
        return Gaussian(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return Gaussian(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-gaussian(other))

    def __rsub__(self, other):
        return gaussian(other) + (-self)

    def __mul__(self, other):
        other = gaussian(other)
        return Gaussian(self.re * other.re - self.im * other.im,
                        self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = gaussian(other)
        norm = other.re**2 + other.im**2
        if not norm:
            raise ZeroDivisionError("Division by zero in Q(i)")
        return self * Gaussian(other.re / norm, -other.im / norm)

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Only nonnegative integer powers are implemented")
        result, base = ONE, self
        while exponent:
            if exponent & 1:
                result *= base
            base *= base
            exponent //= 2
        return result

    def conjugate(self):
        return Gaussian(self.re, -self.im)

    def norm_squared(self):
        return self.re**2 + self.im**2

    def encode(self):
        return [str(self.re), str(self.im)]


def gaussian(value):
    return value if isinstance(value, Gaussian) else Gaussian(Q(value))


ZERO, ONE, I = Gaussian(), Gaussian(1), Gaussian(0, 1)
ROOTS4 = frozenset((ONE, -ONE, I, -I))


def admissible_letter(a):
    """A rational test for the two disks condition, including letters 0,1."""
    a = gaussian(a)
    return a in (ZERO, ONE) or (
        a.norm_squared() >= 1 and (ONE - a).norm_squared() >= 1)


def check_word(word):
    word = tuple(map(gaussian, word))
    if word and (word[0] == ONE or word[-1] == ZERO):
        raise ValueError("Need first letter != 1 and last letter != 0")
    if not all(admissible_letter(a) for a in word):
        raise ValueError("A letter or its reflection is inside the unit disk")
    return word


def extend_coefficients(a, tail):
    """Prepend a letter to Taylor coefficients already evaluated at 1/2.

    Input tail[n] = 2**(-n) [x**n] G(tail_word;x).
    The returned list uses the same normalization for G(a,tail_word;x).
    """
    cutoff = len(tail) - 1
    result = [ZERO] * (cutoff + 1)
    if a == ZERO:
        if tail[0] != ZERO:
            raise ValueError("An all-zero word needs logarithmic regularization")
        for n in range(1, cutoff + 1):
            result[n] = tail[n] / n
    else:
        half_inverse = ONE / (2 * a)
        for n in range(cutoff):
            result[n + 1] = (n * result[n] - tail[n]) * half_inverse / (n + 1)
    return result


def binomial_tail(depth, cutoff):
    """Exactly sum_{n>cutoff} binom(n-1,depth-1) 2**(-n)."""
    if depth == 0:
        return Q(0)
    return Q(sum(comb(cutoff, k) for k in range(min(depth, cutoff + 1))),
             2**cutoff)


def split_depths(word):
    w = len(word)
    left, right = [0] * (w + 1), [0] * (w + 1)
    for j in range(w - 1, -1, -1):
        right[j] = right[j + 1] + (word[j] != ZERO)
    for j in range(1, w + 1):
        left[j] = left[j - 1] + (word[j - 1] != ONE)
    return left, right


def error_bound(word, cutoff):
    left, right = split_depths(word)
    # Compute every needed T_d in one pass, rather than recomputing binomials
    # for each cut.  The center and its radius both take O(weight * cutoff)
    # arithmetic operations (the radius alone takes O(weight)).
    tails, cumulative, term = [Q(0)], 0, 1
    denominator = 2**cutoff
    for k in range(len(word)):
        cumulative += term
        tails.append(Q(cumulative, denominator))
        term = term * (cutoff-k) // (k+1) if k < cutoff else 0
    return sum((tails[d] for d in left + right), Q(0))


def choose_cutoff(word, bits):
    """Smallest cutoff passing the proved word-sensitive rational bound."""
    if not isinstance(bits, int) or bits < 1:
        raise ValueError("bits must be a positive integer")
    if not word:
        return 0
    w = len(word)
    low, high = 0, 3 * (bits + w + w.bit_length())
    tolerance = Q(1, 2**bits)
    assert error_bound(word, high) <= tolerance
    while low < high:
        middle = (low + high) // 2
        if error_bound(word, middle) <= tolerance:
            high = middle
        else:
            low = middle + 1
    return low


def evaluate_at_cutoff(word, cutoff):
    """Exact Hoelder center and error.  Work: O(weight * cutoff) Q(i) ops."""
    word = check_word(word)
    if not isinstance(cutoff, int) or cutoff < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    w = len(word)
    if not w:
        return ONE, Q(0)
    empty = [ONE] + [ZERO] * cutoff
    right, left = [ONE] * (w + 1), [ONE] * (w + 1)
    coefficients = empty
    for j in range(w - 1, -1, -1):
        coefficients = extend_coefficients(word[j], coefficients)
        right[j] = sum(coefficients, ZERO)
    coefficients = empty
    for j in range(1, w + 1):
        coefficients = extend_coefficients(ONE - word[j - 1], coefficients)
        left[j] = sum(coefficients, ZERO)
    center = sum(((-1)**j * left[j] * right[j] for j in range(w + 1)), ZERO)
    return center, error_bound(word, cutoff)


@dataclass(frozen=True)
class Certificate:
    word: tuple
    cutoff: int
    center: Gaussian
    radius: Q
    prefactor: int = 1

    def real(self):
        return Interval(self.center.re - self.radius, self.center.re + self.radius)

    def imag(self):
        return Interval(self.center.im - self.radius, self.center.im + self.radius)

    def encode(self):
        return {"word": [a.encode() for a in self.word], "cutoff": self.cutoff,
                "prefactor": self.prefactor,
                "center": self.center.encode(), "radius": str(self.radius),
                "meaning": "abs(prefactor * G(word;1) - center) <= radius; exact rationals"}


def certified_gpl(word, bits=384):
    word = check_word(word)
    cutoff = choose_cutoff(word, bits)
    center, radius = evaluate_at_cutoff(word, cutoff)
    return Certificate(word, cutoff, center, radius)


def mpl_word(indices, colors):
    """Outer-first decreasing-index MPL to GPL with prefix-product letters."""
    if not indices or len(indices) != len(colors):
        raise ValueError("Require nonempty index/color lists of equal length")
    prefix, word = ONE, []
    for index, color in zip(indices, colors):
        if not isinstance(index, int) or index < 1:
            raise ValueError("Indices must be positive integers")
        color = gaussian(color)
        if color not in ROOTS4:
            raise ValueError("This interface accepts fourth roots of unity")
        prefix *= color
        word.extend([ZERO] * (index - 1))
        word.append(ONE / prefix)
    return tuple(word)


def certified_mpl(indices, colors, bits=384):
    cert = certified_gpl(mpl_word(indices, colors), bits)
    return Certificate(cert.word, cert.cutoff,
                       (-1)**len(indices) * cert.center, cert.radius,
                       (-1)**len(indices))


@dataclass(frozen=True)
class Interval:
    """Closed rational interval with outward rounding supplied by exactness."""

    low: Q
    high: Q

    def __post_init__(self):
        object.__setattr__(self, "low", Q(self.low))
        object.__setattr__(self, "high", Q(self.high))
        if self.low > self.high:
            raise ValueError("Interval endpoints out of order")

    def __add__(self, other):
        other = interval(other)
        return Interval(self.low + other.low, self.high + other.high)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return self + (-interval(other))

    def __rsub__(self, other):
        return interval(other) + (-self)

    def __mul__(self, other):
        other = interval(other)
        products = [x*y for x in (self.low, self.high)
                    for y in (other.low, other.high)]
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        if other.low <= 0 <= other.high:
            raise ZeroDivisionError("Interval divisor contains zero")
        return self * Interval(1 / other.high, 1 / other.low)

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Require a nonnegative integer exponent")
        result = interval(1)
        for _ in range(exponent):
            result *= self
        return result

    def contains_zero(self):
        return self.low <= 0 <= self.high

    def max_abs(self):
        return max(abs(self.low), abs(self.high))

    def encode(self):
        return {"low": str(self.low), "high": str(self.high)}


def interval(value):
    return value if isinstance(value, Interval) else Interval(Q(value), Q(value))
