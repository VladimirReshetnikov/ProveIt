"""Sharp cubic-moment and Radau bounds for real Gaussian quadratic forms.

All exponent routines return -log of a Chernoff upper bound, not an exact
tail probability.  Input moments must be exact or otherwise certified.
The floating-point implementation is a reference implementation, not
outward-rounded interval arithmetic.  See the accompanying article.
Normalized moment violations no larger than 1e-12 are clipped to the
feasible interval. Saddles that round to a singular endpoint are evaluated
at the adjacent interior float, giving a slightly weaker Chernoff rate.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Iterable


_MOMENT_TOLERANCE = 1e-12
_BELOW_ONE = math.nextafter(1.0, 0.0)


def _finite(value: float, name: str) -> float:
    value = float(value)
    if not math.isfinite(value):
        raise ValueError(f"{name} must be finite")
    return value


def _nonnegative(value: float, name: str) -> float:
    value = _finite(value, name)
    if value < 0.0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def _balance(s: float) -> float:
    """Validate, consistently clipping endpoint roundoff of at most 1e-12."""
    s = _finite(s, "s")
    if not -1.0 - _MOMENT_TOLERANCE <= s <= 1.0 + _MOMENT_TOLERANCE:
        raise ValueError("Require -1<=s<=1")
    return min(1.0, max(-1.0, s))


def _moment_pair(s: float, k: float) -> tuple[float, float]:
    s = _balance(s)
    k = _finite(k, "k")
    if not s * s - _MOMENT_TOLERANCE <= k <= 1.0 + _MOMENT_TOLERANCE:
        raise ValueError("Require s^2<=k<=1")
    return s, min(1.0, max(s * s, k))


def _positive_product_ratio(a: float, b: float, c: float) -> float:
    """Compute a*b/c without an avoidable intermediate overflow."""
    if a == 0.0 or b == 0.0:
        return 0.0
    ma, ea = math.frexp(a)
    mb, eb = math.frexp(b)
    mc, ec = math.frexp(c)
    try:
        return math.ldexp(ma * mb / mc, ea + eb - ec)
    except OverflowError as error:
        raise ValueError("Normalized scale exceeds floating-point range") from error


def phi(y: float) -> float:
    """(-log(1-y)-y)/2, with its cancellation-free small-y series."""
    y = float(y)
    if math.isnan(y):
        raise ValueError("y must not be NaN")
    if y == -math.inf:
        return math.inf
    if y >= 1.0:
        return math.inf
    if abs(y) < 1e-4:
        power = y * y
        total = 0.0
        for j in range(2, 18):
            total += power / (2.0 * j)
            power *= y
        return total
    return 0.5 * (-math.log1p(-y) - y)


def kernel(z: float, x: float) -> float:
    """Variance-weighted Gaussian log-MGF kernel; removable value at x=0."""
    z, x = _finite(z, "z"), _finite(x, "x")
    if x == 0.0:
        return (z / 2.0) * (z / 2.0)
    if abs(z * x) < 1e-4:
        total = 0.0
        power = 1.0
        for j in range(18):
            total += power / (2.0 * (j + 2))
            power *= z * x
        return (z * total) * z
    return (phi(z * x) / x) / x


def signed_cgf(s: float, z: float) -> float:
    """Normalized signed-endpoint log-MGF H_s(z)."""
    s, z = _balance(s), _nonnegative(z, "z")
    plus = 0.0 if s == -1.0 else 0.5 * (1.0 + s) * phi(z)
    minus = 0.0 if s == 1.0 else 0.5 * (1.0 - s) * phi(-z)
    return plus + minus


def signed_saddle(s: float, u: float) -> float:
    s, u = _balance(s), _nonnegative(u, "u")
    if s == -1.0:
        return u / (1.0 - u) if u < 1.0 else math.inf
    # sqrt(1+4u(u+s))/2 = hypot(u+s/2, sqrt(1-s^2)/2).
    # This form avoids squaring u or forming 2u, even near float's limit.
    denominator = 0.5 + math.hypot(
        u + s / 2.0, math.sqrt((1.0 - s) * (1.0 + s)) / 2.0)
    # The exact saddle is below 1; rounding it to 1 would make the CGF
    # infinite and incorrectly collapse the computed rate to zero.
    return min(_BELOW_ONE, u / denominator)


def signed_rate(s: float, u: float) -> float:
    """Numerical J_s(u), including the negative-projection endpoint s=-1."""
    s, u = _balance(s), _nonnegative(u, "u")
    if u == 0.0:
        return 0.0
    if s == -1.0:
        return phi(u) if u < 1.0 else math.inf
    if s == 1.0:
        return phi(-u)
    z = signed_saddle(s, u)
    return max(0.0, u * z / 2.0 - signed_cgf(s, z))


def sharp_constant(s: float) -> float:
    """Optimal constant for a fixed cubic spectral balance s."""
    return min(0.25, signed_rate(s, 1.0))


@dataclass(frozen=True)
class Moments:
    L: float
    v: float
    p3: float
    p4: float

    def __post_init__(self) -> None:
        for name in ("L", "v", "p3", "p4"):
            object.__setattr__(self, name, _finite(getattr(self, name), name))
        if self.L <= 0.0 or self.v <= 0.0:
            raise ValueError("A nonzero quadratic form requires L>0 and v>0")
        _moment_pair(self.s, (self.p4 / self.v / self.L) / self.L)
        if not math.isfinite(self.r) or self.r <= 0.0:
            raise ValueError("Normalized variance is outside floating-point range")

    @property
    def r(self) -> float:
        return (self.v / self.L) / self.L

    @property
    def s(self) -> float:
        return _balance((self.p3 / self.v) / self.L)

    @property
    def k(self) -> float:
        return _moment_pair(self.s, (self.p4 / self.v / self.L) / self.L)[1]

    def exponent(self, t: float, order: int = 4) -> float:
        """Upper-tail exponent for Q >= t, using two, three, or four moments."""
        t = _nonnegative(t, "t")
        u = _positive_product_ratio(t, self.L, self.v)
        if order == 2:
            return self.r * signed_rate(1.0, u)
        if order == 3:
            return self.r * signed_rate(self.s, u)
        if order == 4:
            return self.r * radau_rate(self.s, self.k, u)
        raise ValueError("order must be 2, 3, or 4")

    def reflected(self) -> "Moments":
        return Moments(self.L, self.v, -self.p3, self.p4)


def spectral_moments(eigenvalues: Iterable[float], L: float | None = None) -> Moments:
    values = tuple(_finite(x, "eigenvalue") for x in eigenvalues)
    if not values:
        raise ValueError("At least one eigenvalue is required")
    actual = max(abs(x) for x in values)
    if L is None:
        L = actual
    else:
        L = _finite(L, "L")
    if L < actual:
        raise ValueError("L is not an upper bound for the operator norm")
    return Moments(L, math.fsum(x * x for x in values),
                   math.fsum(x ** 3 for x in values),
                   math.fsum(x ** 4 for x in values))


def radau_nodes(s: float, k: float) -> tuple[float, float]:
    """Return interior node a and endpoint mass w at 1."""
    s, k = _moment_pair(s, k)
    if s == 1.0:
        return 1.0, 1.0
    variance = k - s * s
    if variance == 0.0:
        return s, 0.0
    if k == 1.0:
        return -1.0, (1.0 + s) / 2.0
    a = min(1.0, max(-1.0, s - variance / (1.0 - s)))
    # The equivalent denominator 1-2s+k suffers cancellation near s=1.
    w = variance / ((1.0 - s) ** 2 + variance)
    return a, w


def radau_cgf(s: float, k: float, z: float) -> float:
    z = _nonnegative(z, "z")
    a, w = radau_nodes(s, k)
    return (0.0 if w == 1.0 else (1.0 - w) * kernel(z, a)) + (
        0.0 if w == 0.0 else w * kernel(z, 1.0))


def radau_saddle(s: float, k: float, u: float) -> float:
    s, k = _moment_pair(s, k)
    u = _nonnegative(u, "u")
    if s == 1.0:
        return min(_BELOW_ONE, u / (1.0 + u))
    a, w = radau_nodes(s, k)
    if w == 0.0:
        denominator = 1.0 + u * a
        return u / denominator if denominator > 0.0 else math.inf
    variance_root = math.sqrt(k - s * s)
    coefficient = 2.0 * s - 1.0 - a
    if u >= 1.0:
        inverse_u = 1.0 / u
        denominator = (inverse_u + 1.0 + a + math.hypot(
            inverse_u + coefficient, 2.0 * variance_root)) / 2.0
        saddle = 1.0 / denominator
    else:
        discriminant_root = math.hypot(
            1.0 + u * coefficient, 2.0 * u * variance_root)
        saddle = 2.0 * u / (1.0 + u * (1.0 + a) + discriminant_root)
    return min(_BELOW_ONE, saddle)


def radau_rate(s: float, k: float, u: float) -> float:
    """Numerical Radau Chernoff rate, with removable and bounded-tail cases."""
    s, k = _moment_pair(s, k)
    u = _nonnegative(u, "u")
    if u == 0.0:
        return 0.0
    if s == 1.0:
        return signed_rate(1.0, u)
    a, w = radau_nodes(s, k)
    if w == 0.0:
        if a == 0.0:
            return (u / 2.0) * (u / 2.0)
        if 1.0 + u * a <= 0.0:
            return math.inf
        return kernel(-u, a)
    z = radau_saddle(s, k, u)
    return max(0.0, u * z / 2.0 - radau_cgf(s, k, z))


def radau_constant(s: float, k: float) -> float:
    """Optimal HW coefficient of the Radau CGF envelope.

    This is envelope optimality. Sharpness for every exact finite-matrix
    moment tuple additionally requires spectral realizability.
    """
    return min(0.25, radau_rate(s, k, 1.0))


def exact_cgf(eigenvalues: Iterable[float], theta: float) -> float:
    theta = _finite(theta, "theta")
    return math.fsum(phi(2.0 * (theta * _finite(x, "eigenvalue")))
                     for x in eigenvalues)


def deficit_coefficient(z: float) -> float:
    """Sharp chord-defect coefficient D(z), 0<=z<1."""
    if not 0.0 <= z < 1.0:
        raise ValueError("Require 0<=z<1")
    if z < 0.02:
        # 1/((1-y)(1+y)^2) has coefficients 1,-1,2,-2,3,-3,...
        return 0.5 * math.fsum(
            ((-1.0) ** j) * (j // 2 + 1) * z ** (j + 4) / (j + 4)
            for j in range(24))
    return (-z / 2.0 - math.log1p(-z) / 8.0
            + 5.0 * math.log1p(z) / 8.0
            + 1.0 / (4.0 * (1.0 + z)) - 0.25)


def two_sided_bound(moments: Moments, t: float, order: int = 4) -> float:
    return min(1.0, math.exp(-moments.exponent(t, order))
               + math.exp(-moments.reflected().exponent(t, order)))


def sample_count(moments: Moments, tolerance: float, failure: float, order: int = 4) -> int:
    """Sufficient independent Gaussian probes for an absolute trace error.

    Uses a common split failure/2 in the two tails. This is a guarantee for
    the ordinary Gaussian sample mean, not an optimal trace-query algorithm.
    """
    tolerance = _finite(tolerance, "tolerance")
    failure = _finite(failure, "failure")
    if tolerance <= 0.0 or not 0.0 < failure < 1.0:
        raise ValueError("Require positive tolerance and 0<failure<1")
    rate = min(moments.exponent(tolerance, order),
               moments.reflected().exponent(tolerance, order))
    if rate <= 0.0:
        raise ArithmeticError("Tail exponent underflowed; use higher precision")
    return max(1, math.ceil((math.log(2.0) - math.log(failure)) / rate))
