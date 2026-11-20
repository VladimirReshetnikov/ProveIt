"""Exact finite reference computations for certified coupled contractions.

All quantities used in inequalities are fractions.Fraction or integers.
These programs replay finite cases. They are not proofs of the universal
theorems in the accompanying report or embedded iPRA derivations.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from typing import Iterable, Sequence

Scalar = int | F
Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]


class CertificateError(ValueError):
    """A finite numerical certificate or its coding is invalid."""


def _nat(value: int, label: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise CertificateError(f"{label} must be an integer >= {minimum}")
    return value


def exact(value: Scalar) -> F:
    """Accept exact inputs only: floats and booleans are deliberately rejected."""
    if isinstance(value, bool) or not isinstance(value, (int, F)):
        raise CertificateError("rational inputs must be int or Fraction")
    return F(value)


def vector(values: Iterable[Scalar], size: int | None = None) -> Vector:
    try:
        result = tuple(exact(x) for x in values)
    except TypeError as exc:
        raise CertificateError("a vector must be an iterable") from exc
    if not result:
        raise CertificateError("zero-dimensional vectors are not in this interface")
    if size is not None and len(result) != size:
        raise CertificateError("vector dimension mismatch")
    return result


def matrix(rows: Iterable[Iterable[Scalar]]) -> Matrix:
    try:
        result = tuple(vector(row) for row in rows)
    except TypeError as exc:
        raise CertificateError("a matrix must be an iterable of rows") from exc
    if not result:
        raise CertificateError("zero-dimensional matrices are not in this interface")
    if any(len(row) != len(result) for row in result):
        raise CertificateError("a square matrix with nonempty equal-length rows is required")
    return result


def add(x: Sequence[Scalar], y: Sequence[Scalar]) -> Vector:
    a = vector(x)
    b = vector(y, len(a))
    return tuple(u + v for u, v in zip(a, b))


def sub(x: Sequence[Scalar], y: Sequence[Scalar]) -> Vector:
    a = vector(x)
    b = vector(y, len(a))
    return tuple(u - v for u, v in zip(a, b))


def scale(c: Scalar, x: Sequence[Scalar]) -> Vector:
    c = exact(c)
    return tuple(c * u for u in vector(x))


def matvec(A: Iterable[Iterable[Scalar]], x: Sequence[Scalar]) -> Vector:
    A = matrix(A)
    x = vector(x, len(A))
    return tuple(sum((a * b for a, b in zip(row, x)), F(0)) for row in A)


def componentwise_le(x: Sequence[Scalar], y: Sequence[Scalar]) -> bool:
    a = vector(x)
    b = vector(y, len(a))
    return all(u <= v for u, v in zip(a, b))


def norm_w(x: Sequence[Scalar], w: Sequence[Scalar]) -> F:
    x = vector(x)
    w = vector(w, len(x))
    if any(v <= 0 for v in w):
        raise CertificateError("norm weights must be strictly positive")
    return max(abs(u) / v for u, v in zip(x, w))


def dyadic(exponent: int) -> F:
    """Return 2**(-exponent) exactly, with exponent a natural number."""
    return F(1, 1 << _nat(exponent, "dyadic exponent"))


def ceil_fraction(x: Scalar) -> int:
    x = exact(x)
    return -((-x.numerator) // x.denominator)


@dataclass(frozen=True)
class GainCertificate:
    A: Matrix
    w: Vector
    s: int

    def __post_init__(self) -> None:
        A = matrix(self.A)
        w = vector(self.w, len(A))
        s = _nat(self.s, "s", 1)
        if any(a < 0 for row in A for a in row):
            raise CertificateError("gain entries must be nonnegative")
        if any(a <= 0 for a in w):
            raise CertificateError("gain weights must be strictly positive")
        q = F(s - 1, s)
        if not componentwise_le(matvec(A, w), scale(q, w)):
            raise CertificateError("the gain inequality A w <= (1 - 1/s) w fails")
        object.__setattr__(self, "A", A)
        object.__setattr__(self, "w", w)
        object.__setattr__(self, "s", s)

    @property
    def q(self) -> F:
        return F(self.s - 1, self.s)

    @property
    def dimension(self) -> int:
        return len(self.w)


@dataclass(frozen=True)
class WeightConstruction:
    certificate: GainCertificate
    m: int
    theta: F
    power_on_ones: Vector


def derive_weights(A: Iterable[Iterable[Scalar]], m: int,
                   theta: Scalar) -> WeightConstruction:
    """Use a supplied m with A^m 1 <= theta 1; no search over m is performed.

    w = sum_{j < m} A^j 1, s = ceil(max_i w_i / (1-theta)).
    The final GainCertificate checks the derived inequality independently.
    """
    A = matrix(A)
    if any(a < 0 for row in A for a in row):
        raise CertificateError("gain entries must be nonnegative")
    m = _nat(m, "power horizon", 1)
    theta = exact(theta)
    if not F(0) <= theta < F(1):
        raise CertificateError("theta must satisfy 0 <= theta < 1")
    power = tuple(F(1) for _ in A)
    w = tuple(F(0) for _ in A)
    for _ in range(m):
        w = add(w, power)
        power = matvec(A, power)
    if any(a > theta for a in power):
        raise CertificateError("the supplied finite-power certificate fails")
    s = max(1, ceil_fraction(max(w) / (1 - theta)))
    result = GainCertificate(A, w, s)
    return WeightConstruction(result, m, theta, power)


@dataclass(frozen=True)
class Supersolution:
    z: Vector
    partial_sum: Vector
    tail: Vector
    tail_norm: F
    slack: Vector
    N: int


def neumann_supersolution(cert: GainCertificate,
                         rho: Sequence[Scalar], N: int) -> Supersolution:
    """Compute z_N = sum_{j<N} A^j rho + s ||A^N rho||_w w.

    N=0 is valid. Exact verification checks z_N >= A z_N + rho.
    """
    rho = vector(rho, cert.dimension)
    if any(a < 0 for a in rho):
        raise CertificateError("the residual majorant must be nonnegative")
    N = _nat(N, "Neumann horizon")
    tail = rho
    partial = tuple(F(0) for _ in rho)
    for _ in range(N):
        partial = add(partial, tail)
        tail = matvec(cert.A, tail)
    c = norm_w(tail, cert.w)
    z = add(partial, scale(cert.s * c, cert.w))
    slack = sub(z, add(matvec(cert.A, z), rho))
    if any(a < 0 for a in slack):
        raise AssertionError("internal error: constructed Neumann supersolution failed")
    return Supersolution(z, partial, tail, c, slack, N)


@dataclass(frozen=True)
class AffineBox:
    gain: GainCertificate
    b: Vector
    lower: Vector
    upper: Vector

    def __post_init__(self) -> None:
        size = self.gain.dimension
        b = vector(self.b, size)
        lo = vector(self.lower, size)
        hi = vector(self.upper, size)
        if not componentwise_le(lo, hi):
            raise CertificateError("box lower bound exceeds upper bound")
        object.__setattr__(self, "b", b)
        object.__setattr__(self, "lower", lo)
        object.__setattr__(self, "upper", hi)
        if not componentwise_le(lo, self.step(lo)):
            raise CertificateError("lower face does not map inside the box")
        if not componentwise_le(self.step(hi), hi):
            raise CertificateError("upper face does not map inside the box")

    def contains(self, x: Sequence[Scalar]) -> bool:
        x = vector(x, self.gain.dimension)
        return componentwise_le(self.lower, x) and componentwise_le(x, self.upper)

    def step(self, x: Sequence[Scalar]) -> Vector:
        return add(self.b, matvec(self.gain.A, x))

    def iterate(self, initial: Sequence[Scalar], steps: int) -> Vector:
        steps = _nat(steps, "iteration horizon")
        x = vector(initial, self.gain.dimension)
        if not self.contains(x):
            raise CertificateError("initial point is outside the certified box")
        for _ in range(steps):
            x = self.step(x)
            if not self.contains(x):
                raise AssertionError("internal error: certified box was not preserved")
        return x

    def residual(self, x: Sequence[Scalar]) -> F:
        return norm_w(sub(self.step(x), x), self.gain.w)


def coupled_demo() -> tuple[AffineBox, Vector]:
    cert = GainCertificate(((F(0), F(2)), (F(1, 8), F(0))),
                           (F(4), F(1)), 2)
    model = AffineBox(cert, (F(1), F(1, 4)),
                      (F(0), F(0)), (F(4), F(1)))
    root = (F(2), F(1, 2))
    if model.step(root) != root:
        raise AssertionError("incorrect demo fixed point")
    return model, root


def floor_dyadic(x: Scalar, bits: int) -> F:
    """Directed rounding down, including negative inputs."""
    x = exact(x)
    denominator = 1 << _nat(bits, "dyadic bits")
    numerator = (x.numerator * denominator) // x.denominator
    return F(numerator, denominator)


def _box_vector(x: Sequence[Scalar]) -> Vector:
    x = vector(x)
    if any(a < 0 or a > 1 for a in x):
        raise CertificateError("tower coordinates must lie in [0,1]")
    return x


def tower_coefficient(i: int) -> F:
    return F(1, 4 * (_nat(i, "coordinate index") + 1))


def tower_step(x: Sequence[Scalar]) -> Vector:
    """F_{n,i}(x)=a_i+x_i^2/8+x_{i+1}/8, with x_n=0."""
    x = _box_vector(x)
    return tuple(tower_coefficient(i) + a * a / 8
                 + (x[i + 1] if i + 1 < len(x) else F(0)) / 8
                 for i, a in enumerate(x))


def tower_metric(x: Sequence[Scalar], y: Sequence[Scalar]) -> F:
    x = vector(x)
    y = vector(y, len(x))
    return max(dyadic(i) * abs(a - b) for i, (a, b) in enumerate(zip(x, y)))


def tower_iteration(n: int, steps: int, bits: int) -> Vector:
    n = _nat(n, "tower dimension", 1)
    steps = _nat(steps, "iteration horizon")
    bits = _nat(bits, "dyadic bits")
    x = tuple(F(0) for _ in range(n))
    for _ in range(steps):
        exact_next = tower_step(x)
        x = tuple(floor_dyadic(a, bits) for a in exact_next)
        if any(a < 0 or a > 1 for a in x):
            raise AssertionError("internal error: rounded orbit left its box")
    return x


@lru_cache(maxsize=None, typed=True)
def tower_y(n: int) -> Vector:
    """The specified solver: n+4 rounded steps at n+8 fractional bits."""
    n = _nat(n, "tower dimension", 1)
    return tower_iteration(n, n + 4, n + 8)


def tower_residual(n: int) -> F:
    y = tower_y(n)
    return tower_metric(y, tower_step(y))


def tower_residual_budget(n: int) -> F:
    return dyadic(_nat(n, "tower dimension", 1) + 4)


def tower_defect_budget(n: int) -> F:
    return dyadic(_nat(n, "coarse dimension", 1) + 2)


def tower_commutation_defect(fine: Sequence[Scalar], coarse_dimension: int) -> F:
    fine = _box_vector(fine)
    n = _nat(coarse_dimension, "coarse dimension", 1)
    if n >= len(fine):
        raise CertificateError("restriction must strictly lower the dimension")
    return tower_metric(tower_step(fine)[:n], tower_step(fine[:n]))


def tower_adjacent_distance(n: int) -> F:
    n = _nat(n, "tower dimension", 1)
    return tower_metric(tower_y(n), tower_y(n + 1)[:n])


def tower_adjacent_comparison_bound(n: int) -> F:
    """The finite residual/defect estimate, using q=1/2 and L_R=1."""
    n = _nat(n, "tower dimension", 1)
    return 2 * (tower_residual(n) + tower_residual(n + 1)
                + tower_defect_budget(n))


def Q(i: int, k: int) -> F:
    i = _nat(i, "coordinate index")
    k = _nat(k, "precision")
    return tower_y(i + k + 3)[i]


def Q_equation_residual(i: int, k: int) -> F:
    x = Q(i, k)
    neighbor = Q(i + 1, k)
    return abs(x - tower_coefficient(i) - x * x / 8 - neighbor / 8)


def Q_coherence_budget(k: int) -> F:
    """Strong bound for any finer precision, justified by the report's proof."""
    return dyadic(_nat(k, "precision") + 2)


def Q_equation_budget(k: int) -> F:
    return dyadic(_nat(k, "precision") + 4)


def no_gap_epsilon(n: int) -> F:
    return dyadic(_nat(n, "counterexample index") + 2)


def no_gap_fixed_point(n: int) -> F:
    return F(_nat(n, "counterexample index") % 2)


def no_gap_step(n: int, x: Scalar) -> F:
    x = exact(x)
    if not F(0) <= x <= F(1):
        raise CertificateError("counterexample state must lie in [0,1]")
    e = no_gap_epsilon(n)
    return (1 - e) * x + e * no_gap_fixed_point(n)


def no_gap_defect(n: int) -> F:
    """Exact supremum on [0,1]; an affine difference attains it at an endpoint."""
    n = _nat(n, "counterexample index")
    return max(abs(no_gap_step(n + 1, x) - no_gap_step(n, x))
               for x in (F(0), F(1)))


def dyadic_decimal(x: Scalar) -> str:
    """Exact terminating decimal for a dyadic rational, with no floating point."""
    x = exact(x)
    d = x.denominator
    if d & (d - 1):
        raise CertificateError("an exact dyadic decimal requires a power-of-two denominator")
    exponent = d.bit_length() - 1
    sign = "-" if x < 0 else ""
    digits = str(abs(x.numerator) * (5 ** exponent))
    if exponent == 0:
        return sign + digits
    digits = digits.zfill(exponent + 1)
    result = digits[:-exponent] + "." + digits[-exponent:]
    return sign + result.rstrip("0").rstrip(".")

