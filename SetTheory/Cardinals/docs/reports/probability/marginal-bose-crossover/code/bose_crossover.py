"""Numerical evaluation of the marginal anisotropic Bose crossover.

The function evaluated here is

    G(s) = sum(n**(-1) * Psi(s*sqrt(n)), n=1..infinity),
    Psi(u) = integral(exp(-x**4-u*x**2), x=-infinity..infinity).

All computations use mpmath.  ``truncation_error_bound`` is an analytic
bound on omitted mathematical terms, evaluated with ordinary floating
point arithmetic.  It DOES NOT enclose rounding error.  In particular,
the intervals in Approximation are not certified interval-arithmetic
enclosures.  Use the separate Arb implementation for that purpose.

The small-s method is an exact, convergent Mellin-residue expansion.  The
large-s method is an alternating asymptotic expansion, whose finite-term
one-sided error bound holds for every positive s.  The accelerated method
evaluates a finite positive sum and applies that same expansion only to
the remaining tail.  It therefore remains accurate beyond the disk of
convergence of the small-s expansion.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from mpmath import mp


@dataclass(frozen=True)
class Approximation:
    """Value and a truncation-only bound, with reproducibility metadata."""

    value: object
    truncation_error_bound: object
    lower: object
    upper: object
    method: str
    degree: int
    direct_terms: int
    precision_digits: int
    rounding_certified: bool = False

    @property
    def midpoint(self):
        return (self.lower + self.upper) / 2


@dataclass(frozen=True)
class TemperatureBracket:
    """Numerical application of the analytic density-to-temperature bound.

    Even if the supplied density bounds are rigorous, mpmath arithmetic
    in the conversion is not outward rounded.  The separate Arb module
    is required for a certified floating-point temperature enclosure.
    """

    lower: object
    upper: object
    trial_temperature: object
    density_ratio_lower: object
    density_ratio_upper: object
    precision_digits: int
    rounding_certified: bool = False


def _positive(value, name):
    value = mp.mpf(value)
    if not mp.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and strictly positive")
    return value


def convergence_radius():
    return mp.sqrt(8 * mp.pi)


def psi(u):
    """Evaluate Psi(u) by its Bessel-K representation, for u >= 0."""
    u = mp.mpf(u)
    if not mp.isfinite(u) or u < 0:
        raise ValueError("u must be finite and nonnegative")
    if u == 0:
        return mp.gamma(mp.mpf(1) / 4) / 2
    theta = u * u / 8
    return mp.sqrt(u) * mp.exp(theta) * mp.besselk(mp.mpf(1) / 4, theta) / 2


def logarithmic_part(s):
    """The double-pole contribution to G(s)."""
    s = _positive(s, "s")
    return mp.gamma(mp.mpf(1) / 4) * (
        -mp.log(s) + mp.pi / 4 + mp.mpf(3) * mp.log(2) / 2
    )


def _cos_pi_k_over_four(k):
    """An exact zero pattern; do not compute cos(k*pi/4) numerically."""
    h = mp.sqrt(mp.mpf(1) / 2)
    return (mp.mpf(1), h, mp.mpf(0), -h, -mp.mpf(1), -h, mp.mpf(0), h)[k % 8]


def regular_coefficient(k):
    """Coefficient of s**k in G(s) minus logarithmic_part(s).

    k=2 is handled before applying the zeta functional equation: the
    latter would otherwise contain the indeterminate product 0*zeta(1).
    The trivial-zeta-zero coefficients k=6,10,14,... are exactly zero.
    """
    if not isinstance(k, int) or k < 1:
        raise ValueError("k must be a positive integer")
    quarter = mp.mpf(1) / 4
    if k == 1:
        return -mp.gamma(3 * quarter) * mp.zeta(mp.mpf(1) / 2) / 2
    if k == 2:
        return -mp.gamma(quarter) / 32
    cosine = _cos_pi_k_over_four(k)
    if cosine == 0:
        return mp.mpf(0)
    half_k = mp.mpf(k) / 2
    # Positive zeta arguments avoid increasingly ill-conditioned direct
    # evaluation near the trivial zeros at large negative arguments.
    return (
        (-1) ** k * cosine * mp.zeta(half_k)
        * mp.exp(mp.loggamma(half_k) + mp.loggamma(half_k + quarter)
                 - mp.loggamma(k + 1) - half_k * mp.log(2 * mp.pi))
    )


def normalized_coefficient(k):
    """Coefficient b_k in 2G(s)/Gamma(1/4) after its log and constant."""
    return 2 * regular_coefficient(k) / mp.gamma(mp.mpf(1) / 4)


def small_s_remainder_bound(s, degree):
    """Bound after all residues k=0,...,degree, using a half-integer line.

    The bound is valid for s > 0 even outside the convergence disk.  Only
    for s <= sqrt(8*pi) is its convergence to zero asserted.
    """
    s = _positive(s, "s")
    if not isinstance(degree, int) or degree < 2:
        raise ValueError("degree must be an integer at least 2")
    c = mp.mpf(degree) + mp.mpf(1) / 2
    ratio = mp.exp(mp.loggamma(c / 2 + mp.mpf(1) / 4)
                   - mp.loggamma(c / 2 + mp.mpf(1) / 2))
    return (mp.sqrt(mp.pi) / mp.cos(mp.pi / 8) * mp.zeta(c / 2)
            * ratio / c * (s / convergence_radius()) ** c)


def small_s_expansion(s, degree):
    """A finite small-s expansion, with an explicit truncation bound."""
    s = _positive(s, "s")
    bound = small_s_remainder_bound(s, degree)
    value = logarithmic_part(s) + mp.fsum(
        regular_coefficient(k) * s ** k for k in range(1, degree + 1)
    )
    return Approximation(value, bound, value - bound, value + bound,
                         "small-s Mellin series", degree, 0, mp.dps)


def _asymptotic_term(s, j, tail_start=1):
    """Unsigned j-th coefficient of the tail n >= tail_start."""
    p = j + mp.mpf(5) / 4
    # mpmath's general Hurwitz-zeta algorithm can lose *relative*
    # accuracy when a**(-p) is far below its working absolute epsilon.
    # The large gamma factor would amplify that error.  Supply enough
    # guard precision to retain accuracy before rescaling the tiny zeta.
    extra = 20 + max(0, int(mp.ceil(p * mp.log10(tail_start))))
    with mp.extradps(extra):
        hurwitz = mp.zeta(p, tail_start)
    return (mp.exp(mp.loggamma(2 * j + mp.mpf(1) / 2)
                   - mp.loggamma(j + 1)
                   - (2 * j + mp.mpf(1) / 2) * mp.log(s))
            * hurwitz)


def large_s_expansion(s, terms, *, tail_start=1):
    """Expand sum_{n>=tail_start} n^-1 Psi(s*sqrt(n)).

    ``terms`` is the number M of included terms, j=0,...,M-1.  The omitted
    remainder has sign (-1)**M and magnitude at most the M-th term.  This
    statement is valid for every s>0 and every M>=1; the asymptotic series
    itself is generally divergent.
    """
    s = _positive(s, "s")
    if not isinstance(terms, int) or terms < 1:
        raise ValueError("terms must be a positive integer")
    if not isinstance(tail_start, int) or tail_start < 1:
        raise ValueError("tail_start must be a positive integer")
    value = mp.fsum((-1) ** j * _asymptotic_term(s, j, tail_start)
                    for j in range(terms))
    bound = _asymptotic_term(s, terms, tail_start)
    if terms % 2:
        lower, upper = value - bound, value
    else:
        lower, upper = value, value + bound
    return Approximation(value, bound, lower, upper,
                         "alternating large-s expansion", terms - 1,
                         0, mp.dps)


def accelerated_positive_sum(s, *, abs_tol=None, direct_terms=None,
                             tail_terms=None):
    """Finite Bessel sum plus a rigorously bounded asymptotic tail.

    The default allocation is M=max(1,ceil(log2(sqrt(pi)/tol))) and
    N=max(1,ceil(4*M/s**2)).  It ensures an error at most sqrt(pi)*2**(-M),
    by elementary gamma and Hurwitz-zeta bounds.  For fixed positive s,
    N=O(log(1/tol)/s**2) direct terms and M=O(log(1/tol)) tail terms suffice.
    These are special-function evaluation counts, not bit-operation claims.
    """
    s = _positive(s, "s")
    tol = _positive(abs_tol if abs_tol is not None else mp.power(10, 12 - mp.dps),
                    "abs_tol")
    if tail_terms is None:
        tail_terms = max(1, int(mp.ceil(mp.log(mp.sqrt(mp.pi) / tol, 2))))
    if not isinstance(tail_terms, int) or tail_terms < 1:
        raise ValueError("tail_terms must be a positive integer")
    if direct_terms is None:
        direct_terms = max(1, int(mp.ceil(4 * tail_terms / (s * s))))
        # The analytic bound, not the heuristic allocation, determines
        # whether the requested tolerance has been reached.
        while _asymptotic_term(s, tail_terms, direct_terms + 1) > tol:
            direct_terms = max(direct_terms + 1, int(mp.ceil(1.25 * direct_terms)))
    if not isinstance(direct_terms, int) or direct_terms < 0:
        raise ValueError("direct_terms must be a nonnegative integer")
    finite = mp.fsum(psi(s * mp.sqrt(n)) / n
                     for n in range(1, direct_terms + 1))
    tail = large_s_expansion(s, tail_terms, tail_start=direct_terms + 1)
    return Approximation(finite + tail.value, tail.truncation_error_bound,
                         finite + tail.lower, finite + tail.upper,
                         "positive sum with alternating tail", tail_terms - 1,
                         direct_terms, mp.dps)


def evaluate(s, *, abs_tol=None, method="auto", max_degree=20000):
    """Evaluate G(s) with a requested truncation tolerance.

    Precision should exceed the requested number of reliable digits.
    This routine does not automatically infer or certify roundoff error.
    """
    s = _positive(s, "s")
    tol = _positive(abs_tol if abs_tol is not None else mp.power(10, 12 - mp.dps),
                    "abs_tol")
    if method not in {"auto", "small", "accelerated"}:
        raise ValueError("method must be auto, small, or accelerated")
    use_small = method == "small" or (method == "auto"
                                       and s <= convergence_radius() / 2)
    if use_small:
        if s >= convergence_radius():
            raise ValueError("adaptive small-s evaluation requires s < sqrt(8*pi)")
        degree = 2
        # Determine the required degree before computing the coefficients.
        while small_s_remainder_bound(s, degree) > tol:
            degree += 1
            if degree > max_degree:
                if method == "auto":
                    return accelerated_positive_sum(s, abs_tol=tol)
                raise ArithmeticError("max_degree exceeded before reaching tolerance")
        return small_s_expansion(s, degree)
    return accelerated_positive_sum(s, abs_tol=tol)


def density_prefactor():
    """C in rho(T,delta)=C*T*G(delta/sqrt(T))."""
    return mp.gamma(mp.mpf(1) / 4) / (16 * mp.pi ** (mp.mpf(5) / 2))


def critical_density(temperature, delta, *, abs_tol=None):
    temperature = _positive(temperature, "temperature")
    delta = _positive(delta, "delta")
    scale = density_prefactor() * temperature
    if abs_tol is not None:
        abs_tol = _positive(abs_tol, "abs_tol") / scale
    return scale * evaluate(delta / mp.sqrt(temperature), abs_tol=abs_tol).midpoint


def inverse_parameters(rho, delta):
    """Lambert-W coordinates (b,w,T0) for the critical temperature."""
    rho = _positive(rho, "rho")
    delta = _positive(delta, "delta")
    A = density_prefactor() * mp.gamma(mp.mpf(1) / 4)
    b = 2 * rho / A
    kappa = 8 * mp.exp(mp.pi / 2)
    w = mp.lambertw(kappa * b / (delta * delta)).real
    return b, w, b / w


def inverse_approximation(rho, delta, *, order=2):
    """Small-delta critical-temperature approximation through order 0,1,2.

    The powers are delta powers with Lambert-W-dependent coefficients;
    this is not a Taylor expansion in delta at zero.
    """
    if order not in {0, 1, 2}:
        raise ValueError("order must be 0, 1, or 2")
    delta = _positive(delta, "delta")
    _, w, t0 = inverse_parameters(rho, delta)
    if order == 0:
        return t0
    D = w + 1
    b1 = normalized_coefficient(1)
    answer = t0 - b1 * delta * mp.sqrt(t0) / D
    if order == 2:
        answer += delta * delta * (1 / (16 * D) + b1 * b1 * w / (2 * D ** 3))
    return answer


def critical_temperature(rho, delta, *, relative_tol=None):
    """Solve rho=C*T*G(delta/sqrt(T)) using a bracketed secant method.

    The solution exists and is unique because the occupation integral is
    strictly increasing from zero to infinity in T.  The root returned by
    this mpmath implementation is numerically checked, not interval certified.
    """
    rho = _positive(rho, "rho")
    delta = _positive(delta, "delta")
    tol = _positive(relative_tol if relative_tol is not None
                    else mp.power(10, 15 - mp.dps), "relative_tol")
    _, _, t0 = inverse_parameters(rho, delta)

    def residual(t):
        return critical_density(t, delta, abs_tol=rho * tol / 100) / rho - 1

    lower, upper = t0 / 2, 2 * t0
    while residual(lower) >= 0:
        lower /= 2
    while residual(upper) <= 0:
        upper *= 2
    root = mp.findroot(residual, (lower, upper), solver="anderson",
                       tol=tol / 10, maxsteps=150, verify=False)
    if root <= 0 or abs(residual(root)) > 2 * tol:
        raise ArithmeticError("critical-temperature solver did not meet its residual tolerance")
    return root


def temperature_bracket_from_density(trial_temperature, target_density,
                                     density_lower, density_upper):
    """Convert a density interval at one T into a critical-T interval.

    The exact mathematical result uses 1 < d(log N)/d(log T) < 5/4.
    If ell <= N(T,delta)/target_density <= h, then

      T * min(h**(-1), h**(-4/5)) <= Tc
          <= T * max(ell**(-1), ell**(-4/5)).

    Thus no derivative approximation or interval root iteration is
    needed.  The input interval must refer to the same positive delta
    as the sought critical temperature.  This mpmath conversion excludes
    arithmetic rounding from its guarantee; see TemperatureBracket.
    """
    t = _positive(trial_temperature, "trial_temperature")
    rho = _positive(target_density, "target_density")
    nlo = _positive(density_lower, "density_lower")
    nhi = _positive(density_upper, "density_upper")
    if nlo > nhi:
        raise ValueError("density_lower must not exceed density_upper")
    ell, h = nlo / rho, nhi / rho
    exponent = -mp.mpf(4) / 5
    lower = t * min(1 / h, h**exponent)
    upper = t * max(1 / ell, ell**exponent)
    return TemperatureBracket(lower, upper, t, ell, h, mp.dps)


def direct_sum_tail_upper_bound(s, last_term):
    """Simple upper bound for the unaccelerated positive series tail."""
    s = _positive(s, "s")
    if not isinstance(last_term, int) or last_term < 0:
        raise ValueError("last_term must be a nonnegative integer")
    return mp.sqrt(mp.pi) / mp.sqrt(s) * mp.zeta(mp.mpf(5) / 4, last_term + 1)


def direct_sum_tail_lower_bound(s, last_term):
    """A lower bound, useful for proving the slow positive-sum convergence."""
    s = _positive(s, "s")
    if not isinstance(last_term, int) or last_term < 0:
        raise ValueError("last_term must be a nonnegative integer")
    return max(mp.mpf(0), _asymptotic_term(s, 0, last_term + 1)
               - _asymptotic_term(s, 1, last_term + 1))
