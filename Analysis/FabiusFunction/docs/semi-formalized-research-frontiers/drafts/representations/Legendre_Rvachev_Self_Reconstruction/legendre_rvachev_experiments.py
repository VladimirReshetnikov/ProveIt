#!/usr/bin/env python3
"""Exact and numerical experiments for the Legendre--Rvachev closed loop.

This program accompanies the report

    Legendre--Rvachev Self-Reconstruction on [-1,1]

and is intentionally self-contained.  It has four purposes:

1. compute the moments of Rvachev's up density, reciprocal-MGF coefficients,
   Legendre polynomials P_n, their deconvolved partners Q_n=M(D)^(-1)P_n,
   and the exact rational Fourier--Legendre coefficients u_n;
2. verify the finite literal-shift synthesis of P_n at dyadic test points in
   exact rational arithmetic;
3. verify the new nested-grid null relation and a coarse-to-fine lifting step;
4. generate the CSV tables and figures used by the report.

No quadrature, interpolation, FFT, or sampled approximation enters any exact
identity.  Floating point is used only for large coefficient-variation scans
and plotting.  The only non-standard dependencies are NumPy and Matplotlib,
and the exact checks can still be read independently of those sections.

Normalization
-------------
Let u=up be even, supported on [-1,1], and normalized by integral u=1.  Its
moment generating function is

    M(z) = product_{j>=1} sinh(z/2^j)/(z/2^j).

If

    1/M(z) = sum_{r>=0} beta_r z^r/r!,

then the polynomial deconvolution operator is

    D_u = M(D)^(-1) = sum beta_r D^r/r!.

We write Q_n=D_u P_n.  For a degree-d polynomial p and m=2^d,

    p(x) = (1/m) sum_{|k|<2m} (D_u p)(k/m) u(x-k/m),  -1<=x<=1.

For p=P_{2n}, m=4^n.  The exact Fourier--Legendre expansion is

    u(x) = sum_{n>=0} u_n P_{2n}(x),
    u_n  = (4n+1)/2 * integral_{-1}^1 u(x)P_{2n}(x) dx.

All polynomial coefficients and all u_n are rational.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

# Python 3.11+ limits decimal conversion of huge integers.  Exact output here
# is deliberate, so remove the guard when the interpreter exposes it.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(1_000_000)


# ---------------------------------------------------------------------------
# Exact exponential-generating-function algebra
# ---------------------------------------------------------------------------


def bernoulli_numbers(max_order: int) -> list[Fraction]:
    """Return B_0,...,B_max_order exactly.

    The Akiyama--Tanigawa algorithm used here returns B_1=+1/2.  Only the even
    Bernoulli numbers enter the up cumulants, so the B_1 convention is
    irrelevant to every result below.
    """
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    work = [Fraction(0) for _ in range(max_order + 1)]
    result: list[Fraction] = []
    for m in range(max_order + 1):
        work[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            work[j - 1] = j * (work[j - 1] - work[j])
        result.append(work[0])
    return result


def up_cumulants(max_order: int) -> list[Fraction]:
    r"""Return cumulants kappa_0,...,kappa_max_order of the up density.

    Odd cumulants vanish.  For r>=1,

        kappa_{2r} = B_{2r}/(2r(1-4^{-r}))
                    = 2^(2r-1) B_{2r}/(r(2^(2r)-1)).
    """
    bernoulli = bernoulli_numbers(max_order)
    kappa = [Fraction(0) for _ in range(max_order + 1)]
    for order in range(2, max_order + 1, 2):
        r = order // 2
        kappa[order] = (
            Fraction(2 ** (2 * r - 1), r * (2 ** (2 * r) - 1))
            * bernoulli[order]
        )
    return kappa


def moments_from_cumulants(kappa: Sequence[Fraction]) -> list[Fraction]:
    r"""Convert cumulants to moments using the complete-Bell recurrence.

        mu_n = sum_{j=1}^n binom(n-1,j-1) kappa_j mu_{n-j}.
    """
    max_order = len(kappa) - 1
    mu = [Fraction(0) for _ in range(max_order + 1)]
    mu[0] = Fraction(1)
    for n in range(1, max_order + 1):
        mu[n] = sum(
            Fraction(math.comb(n - 1, j - 1)) * kappa[j] * mu[n - j]
            for j in range(1, n + 1)
        )
    return mu


def up_moments(max_order: int) -> list[Fraction]:
    """Return exact moments mu_n=integral x^n u(x) dx through max_order."""
    return moments_from_cumulants(up_cumulants(max_order))


def reciprocal_mgf_coefficients(
    max_order: int, moments: Sequence[Fraction] | None = None
) -> list[Fraction]:
    r"""Return beta_n in 1/M(z)=sum beta_n z^n/n! exactly.

    If M(z)=sum mu_n z^n/n!, the EGF reciprocal recurrence is

        beta_n = -sum_{j=1}^n binom(n,j) mu_j beta_{n-j}.
    """
    if moments is None:
        moments = up_moments(max_order)
    if len(moments) <= max_order:
        raise ValueError("moment table is too short")
    beta = [Fraction(0) for _ in range(max_order + 1)]
    beta[0] = Fraction(1)
    for n in range(1, max_order + 1):
        beta[n] = -sum(
            Fraction(math.comb(n, j)) * moments[j] * beta[n - j]
            for j in range(1, n + 1)
        )
    return beta


# ---------------------------------------------------------------------------
# Exact polynomial algebra (ascending monomial coefficients)
# ---------------------------------------------------------------------------


def trim_polynomial(p: Sequence[Fraction]) -> list[Fraction]:
    q = [Fraction(c) for c in p]
    if not q:
        return [Fraction(0)]
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return q


def poly_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    result = [Fraction(0) for _ in range(max(len(a), len(b)))]
    for i, value in enumerate(a):
        result[i] += value
    for i, value in enumerate(b):
        result[i] += value
    return trim_polynomial(result)


def poly_scale(p: Sequence[Fraction], scalar: Fraction) -> list[Fraction]:
    return trim_polynomial([Fraction(scalar) * c for c in p])


def poly_xmul(p: Sequence[Fraction]) -> list[Fraction]:
    return [Fraction(0), *[Fraction(c) for c in p]]


def poly_derivative(p: Sequence[Fraction], order: int = 1) -> list[Fraction]:
    if order < 0:
        raise ValueError("order must be nonnegative")
    q = trim_polynomial(p)
    for _ in range(order):
        if len(q) == 1:
            return [Fraction(0)]
        q = [Fraction(i) * q[i] for i in range(1, len(q))]
    return trim_polynomial(q)


def poly_evaluate(p: Sequence[Fraction], x: Fraction | int) -> Fraction:
    value = Fraction(0)
    x = Fraction(x)
    for coefficient in reversed(p):
        value = value * x + coefficient
    return value


def legendre_polynomials(max_degree: int) -> list[list[Fraction]]:
    """Return P_0,...,P_max_degree with P_n(1)=1."""
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    polynomials = [[Fraction(1)]]
    if max_degree == 0:
        return polynomials
    polynomials.append([Fraction(0), Fraction(1)])
    for n in range(1, max_degree):
        next_p = poly_add(
            poly_scale(poly_xmul(polynomials[n]), Fraction(2 * n + 1, n + 1)),
            poly_scale(polynomials[n - 1], Fraction(-n, n + 1)),
        )
        polynomials.append(next_p)
    return polynomials


def deconvolve_polynomial(
    p: Sequence[Fraction], beta: Sequence[Fraction]
) -> list[Fraction]:
    r"""Return M(D)^(-1)p=sum beta_r p^(r)/r!."""
    degree = len(trim_polynomial(p)) - 1
    if len(beta) <= degree:
        raise ValueError("reciprocal-MGF table is too short")
    result = [Fraction(0) for _ in range(degree + 1)]
    for r in range(degree + 1):
        if beta[r] == 0:
            continue
        derivative = poly_derivative(p, r)
        factor = beta[r] / math.factorial(r)
        for j, coefficient in enumerate(derivative):
            result[j] += factor * coefficient
    return trim_polynomial(result)


def polynomial_expectation(
    p: Sequence[Fraction], moments: Sequence[Fraction]
) -> Fraction:
    """Return integral p(x)u(x) dx from exact moments."""
    if len(moments) < len(p):
        raise ValueError("moment table is too short")
    return sum(Fraction(c) * moments[i] for i, c in enumerate(p))


@dataclass(frozen=True)
class SpectralData:
    """Exact Legendre data, with deconvolution computed only as far as needed."""

    max_mode: int
    max_q_degree: int
    moments: tuple[Fraction, ...]
    beta: tuple[Fraction, ...]
    legendre: tuple[tuple[Fraction, ...], ...]
    q_polynomials: tuple[tuple[Fraction, ...], ...]
    u_coefficients: tuple[Fraction, ...]


def build_spectral_data(
    max_mode: int, max_q_degree: int | None = None
) -> SpectralData:
    """Build exact u_n through max_mode and Q_n only through max_q_degree.

    Computing every Q_n up to degree 2*max_mode is much more expensive than
    computing the Legendre coefficients themselves.  Energy experiments need
    many u_n but only the first few deconvolved polynomials, so the two cutoffs
    are deliberately independent.
    """
    if max_mode < 0:
        raise ValueError("max_mode must be nonnegative")
    max_degree = 2 * max_mode
    if max_q_degree is None:
        max_q_degree = max_degree
    if not 0 <= max_q_degree <= max_degree:
        raise ValueError("max_q_degree must lie between 0 and 2*max_mode")
    moments = up_moments(max_degree)
    beta = reciprocal_mgf_coefficients(max_degree, moments)
    legendre = legendre_polynomials(max_degree)
    q_polynomials = [
        deconvolve_polynomial(legendre[n], beta)
        for n in range(max_q_degree + 1)
    ]
    u_coefficients: list[Fraction] = []
    for n in range(max_mode + 1):
        coefficient = Fraction(4 * n + 1, 2) * polynomial_expectation(
            legendre[2 * n], moments
        )
        u_coefficients.append(coefficient)
    return SpectralData(
        max_mode=max_mode,
        max_q_degree=max_q_degree,
        moments=tuple(moments),
        beta=tuple(beta),
        legendre=tuple(tuple(p) for p in legendre),
        q_polynomials=tuple(tuple(q) for q in q_polynomials),
        u_coefficients=tuple(u_coefficients),
    )


# ---------------------------------------------------------------------------
# Exact dyadic evaluator for F and up
# ---------------------------------------------------------------------------


def fabius_dyadic(
    a: int, n: int, moments: Sequence[Fraction] | None = None
) -> Fraction:
    r"""Evaluate F(a/2^n) exactly for 0<=a<=2^n.

    The finite Thue--Morse/moment formula is

      F(a/2^n) = 2^{-n(n+1)/2}/n! *
          sum_{j=0}^{a-1} (-1)^{s_2(j)}
          sum_{r=0}^{floor(n/2)} binom(n,2r) mu_{2r}
                                  (2a-2j-1)^{n-2r}.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    if not 0 <= a <= 2**n:
        raise ValueError("a must satisfy 0 <= a <= 2^n")
    if a == 0:
        return Fraction(0)
    if a == 2**n:
        return Fraction(1)
    if moments is None:
        moments = up_moments(n)
    total = Fraction(0)
    for j in range(a):
        sign = -1 if j.bit_count() & 1 else 1
        inner = sum(
            Fraction(math.comb(n, 2 * r))
            * moments[2 * r]
            * (2 * a - 2 * j - 1) ** (n - 2 * r)
            for r in range(n // 2 + 1)
        )
        total += sign * inner
    denominator = 2 ** (n * (n + 1) // 2) * math.factorial(n)
    return Fraction(total, denominator)


def up_dyadic(
    q: int, n: int, moments: Sequence[Fraction] | None = None
) -> Fraction:
    r"""Evaluate u(q/2^n) exactly; u is zero at and outside +/-1."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if abs(q) >= 2**n:
        return Fraction(0)
    return fabius_dyadic(2**n - abs(q), n, moments)


def fraction_as_dyadic(x: Fraction) -> tuple[int, int]:
    """Return x=q/2^n in lowest terms; reject non-dyadic rationals."""
    x = Fraction(x)
    denominator = x.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"{x} is not dyadic")
    return x.numerator, denominator.bit_length() - 1


class DyadicUpCache:
    """Cache exact up values while sharing one sufficiently long moment table."""

    def __init__(self, max_resolution: int):
        self.moments = up_moments(max_resolution)
        self._cache: dict[tuple[int, int], Fraction] = {}

    def __call__(self, x: Fraction) -> Fraction:
        q, n = fraction_as_dyadic(x)
        key = (q, n)
        if key not in self._cache:
            self._cache[key] = up_dyadic(q, n, self.moments)
        return self._cache[key]


# ---------------------------------------------------------------------------
# Exact verification of synthesis, null relations, and lifting
# ---------------------------------------------------------------------------


def finite_legendre_synthesis_value(
    degree: int,
    x: Fraction,
    legendre: Sequence[Sequence[Fraction]],
    q_polynomials: Sequence[Sequence[Fraction]],
    up_value: DyadicUpCache,
) -> Fraction:
    """Evaluate the finite unit-scale up synthesis of P_degree exactly."""
    m = 2**degree
    q_poly = q_polynomials[degree]
    return sum(
        Fraction(1, m)
        * poly_evaluate(q_poly, Fraction(k, m))
        * up_value(x - Fraction(k, m))
        for k in range(-2 * m + 1, 2 * m)
    )


def verify_legendre_synthesis(
    output_path: Path, max_degree: int = 6
) -> list[dict[str, object]]:
    """Check P_d synthesis exactly on a deterministic dyadic grid."""
    max_resolution = max_degree + 3
    data = build_spectral_data((max_degree + 1) // 2)
    # build_spectral_data above reaches degree 2*ceil(max_degree/2), enough here
    if len(data.legendre) <= max_degree:
        raise AssertionError("internal degree table is too short")
    up_value = DyadicUpCache(max_resolution)
    rows: list[dict[str, object]] = []
    for degree in range(max_degree + 1):
        m = 2**degree
        residual = Fraction(0)
        point_count = 0
        # Include endpoints and off-lattice points.  A denominator 2^(d+2)
        # keeps every atom argument dyadic without making exact F evaluation
        # unnecessarily expensive.
        denominator = 2 ** (degree + 2)
        stride = max(1, denominator // 8)
        for numerator in range(-denominator, denominator + 1, stride):
            x = Fraction(numerator, denominator)
            expected = poly_evaluate(data.legendre[degree], x)
            actual = finite_legendre_synthesis_value(
                degree,
                x,
                data.legendre,
                data.q_polynomials,
                up_value,
            )
            residual = max(residual, abs(actual - expected))
            point_count += 1
        if residual != 0:
            raise AssertionError(
                f"degree-{degree} Legendre synthesis failed: residual {residual}"
            )
        rows.append(
            {
                "degree": degree,
                "m": m,
                "atom_count": 4 * m - 1,
                "dyadic_points": point_count,
                "max_exact_residual": residual,
            }
        )

    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow({**row, "max_exact_residual": format_fraction(row["max_exact_residual"])})
    return rows


def nested_null_value(
    q_poly: Sequence[Fraction],
    coarse_m: int,
    refinement: int,
    x: Fraction,
    up_value: DyadicUpCache,
) -> Fraction:
    r"""Evaluate the exact fine-minus-embedded-coarse null train.

    For fine_m=refinement*coarse_m, the coefficient at k/fine_m is

        (1-refinement*1_{refinement|k}) Q(k/fine_m).

    The omitted common factor 1/fine_m is irrelevant to its vanishing.
    """
    fine_m = refinement * coarse_m
    total = Fraction(0)
    for k in range(-2 * fine_m + 1, 2 * fine_m):
        multiplier = 1 - (refinement if k % refinement == 0 else 0)
        total += (
            multiplier
            * poly_evaluate(q_poly, Fraction(k, fine_m))
            * up_value(x - Fraction(k, fine_m))
        )
    return total


def verify_nested_null_relation(output_path: Path) -> dict[str, object]:
    """Verify the quarter-grid null identity for Q_4 on a dyadic grid."""
    degree = 4
    coarse_m = 2**degree  # 16
    refinement = 4
    fine_m = refinement * coarse_m
    data = build_spectral_data(2)
    q_poly = data.q_polynomials[degree]
    up_value = DyadicUpCache(8)
    residual = Fraction(0)
    points = [Fraction(j, 8) for j in range(-8, 9)]
    for x in points:
        residual = max(
            residual,
            abs(nested_null_value(q_poly, coarse_m, refinement, x, up_value)),
        )
    if residual != 0:
        raise AssertionError(f"nested null relation failed: {residual}")
    row = {
        "polynomial": "P_4",
        "coarse_m": coarse_m,
        "fine_m": fine_m,
        "refinement": refinement,
        "atom_count": 4 * fine_m - 1,
        "dyadic_points": len(points),
        "max_exact_residual": residual,
    }
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(row.keys()))
        writer.writeheader()
        writer.writerow({**row, "max_exact_residual": format_fraction(residual)})
    return row


def verify_lifting_step(output_path: Path) -> dict[str, object]:
    r"""Verify the N=1 -> N=2 fixed-scale lifting formula exactly.

    Let C_N=sum_{n<=N} u_n Q_{2n}.  When m=4^N and the grid is refined by 4,
    the new coefficient vector minus the embedded coarse vector is the sum of

      (1-4*1_{4|k}) C_N(k/(4m))/(4m)      [a null train]

    and

      u_{N+1} Q_{2N+2}(k/(4m))/(4m)       [the new orthogonal detail].
    """
    old_n = 1
    new_n = old_n + 1
    coarse_m = 4**old_n
    fine_m = 4 * coarse_m
    data = build_spectral_data(new_n)

    def combine_c(n: int) -> list[Fraction]:
        degree = 2 * n
        result = [Fraction(0) for _ in range(degree + 1)]
        for mode in range(n + 1):
            q = data.q_polynomials[2 * mode]
            for power, coefficient in enumerate(q):
                result[power] += data.u_coefficients[mode] * coefficient
        return trim_polynomial(result)

    c_old = combine_c(old_n)
    c_new = combine_c(new_n)
    q_detail = data.q_polynomials[2 * new_n]
    u_detail = data.u_coefficients[new_n]

    max_coefficient_residual = Fraction(0)
    for k in range(-2 * fine_m + 1, 2 * fine_m):
        t = Fraction(k, fine_m)
        fine = Fraction(1, fine_m) * poly_evaluate(c_new, t)
        embedded = (
            Fraction(1, coarse_m) * poly_evaluate(c_old, t)
            if k % 4 == 0
            else Fraction(0)
        )
        predicted = (
            Fraction(1 - (4 if k % 4 == 0 else 0), fine_m)
            * poly_evaluate(c_old, t)
            + Fraction(u_detail, fine_m) * poly_evaluate(q_detail, t)
        )
        max_coefficient_residual = max(
            max_coefficient_residual, abs((fine - embedded) - predicted)
        )
    if max_coefficient_residual != 0:
        raise AssertionError(
            f"lifting coefficient identity failed: {max_coefficient_residual}"
        )

    # Functional check at dyadic points: the full update must equal the new
    # Legendre detail u_2 P_4 after the null component cancels.
    up_value = DyadicUpCache(7)
    max_function_residual = Fraction(0)
    for x in (Fraction(j, 8) for j in range(-8, 9)):
        update_value = Fraction(0)
        for k in range(-2 * fine_m + 1, 2 * fine_m):
            t = Fraction(k, fine_m)
            fine = Fraction(1, fine_m) * poly_evaluate(c_new, t)
            embedded = (
                Fraction(1, coarse_m) * poly_evaluate(c_old, t)
                if k % 4 == 0
                else Fraction(0)
            )
            update_value += (fine - embedded) * up_value(x - t)
        expected = u_detail * poly_evaluate(data.legendre[2 * new_n], x)
        max_function_residual = max(
            max_function_residual, abs(update_value - expected)
        )
    if max_function_residual != 0:
        raise AssertionError(
            f"lifting functional identity failed: {max_function_residual}"
        )

    row = {
        "old_N": old_n,
        "new_N": new_n,
        "coarse_m": coarse_m,
        "fine_m": fine_m,
        "fine_atom_count": 4 * fine_m - 1,
        "max_coefficient_residual": max_coefficient_residual,
        "max_function_residual": max_function_residual,
    }
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(row.keys()))
        writer.writeheader()
        writer.writerow(
            {
                **row,
                "max_coefficient_residual": format_fraction(max_coefficient_residual),
                "max_function_residual": format_fraction(max_function_residual),
            }
        )
    return row


# ---------------------------------------------------------------------------
# Tables and figures
# ---------------------------------------------------------------------------


def format_fraction(value: Fraction | object) -> str:
    value = Fraction(value)
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def write_spectral_table(
    output_path: Path, data: SpectralData, max_mode: int
) -> list[dict[str, object]]:
    """Write exact u_n, Q_{2n}(0), central coefficients, and energy partials."""
    if max_mode > data.max_mode:
        raise ValueError("spectral data is too short")
    energy = Fraction(0)
    rows: list[dict[str, object]] = []
    for n in range(max_mode + 1):
        u_n = data.u_coefficients[n]
        q0 = data.q_polynomials[2 * n][0]
        central = u_n * q0 / (4**n)
        term = u_n * u_n / (4 * n + 1)
        energy += term
        rows.append(
            {
                "n": n,
                "degree": 2 * n,
                "m": 4**n,
                "atom_count": 4 * 4**n - 1,
                "u_n_exact": format_fraction(u_n),
                "u_n_decimal": f"{float(u_n):.17g}",
                "Q_2n_at_0_exact": format_fraction(q0),
                "Q_2n_at_0_decimal": f"{float(q0):.17g}",
                "central_atom_exact": format_fraction(central),
                "central_atom_decimal": f"{float(central):.17g}",
                "A2_term_decimal": f"{float(term):.17g}",
                "A2_partial_decimal": f"{float(energy):.17g}",
            }
        )
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def write_energy_table(
    output_path: Path, data: SpectralData, checkpoints: Iterable[int]
) -> list[dict[str, object]]:
    """Write exact positive rational partial sums for A_2."""
    checkpoint_set = set(checkpoints)
    if not checkpoint_set:
        return []
    if max(checkpoint_set) > data.max_mode:
        raise ValueError("spectral data is too short")
    partial = Fraction(0)
    rows: list[dict[str, object]] = []
    for n, u_n in enumerate(data.u_coefficients):
        partial += u_n * u_n / (4 * n + 1)
        if n in checkpoint_set:
            rows.append(
                {
                    "N": n,
                    "A2_partial_exact": format_fraction(partial),
                    "A2_partial_decimal": f"{float(partial):.17g}",
                    "last_positive_term_decimal": f"{float(u_n*u_n/Fraction(4*n+1)):.17g}",
                }
            )
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def block_conditioning_rows(
    data: SpectralData, max_mode: int
) -> list[dict[str, object]]:
    """Scan raw block coefficients on their full literal-shift grids.

    NumPy is used because the n=9 block already has 1,048,575 atoms.  The
    polynomials and u_n are still generated exactly before conversion to
    double precision.
    """
    import numpy as np

    if max_mode > data.max_mode:
        raise ValueError("spectral data is too short")
    rows: list[dict[str, object]] = []
    for n in range(max_mode + 1):
        m = 4**n
        k = np.arange(-2 * m + 1, 2 * m, dtype=np.int64)
        x = k.astype(np.float64) / float(m)
        q_coefficients = np.array(
            [float(c) for c in data.q_polynomials[2 * n]], dtype=np.float64
        )
        q_values = np.polynomial.polynomial.polyval(x, q_coefficients)
        weights = (float(data.u_coefficients[n]) / float(m)) * q_values
        variation = float(np.sum(np.abs(weights), dtype=np.float64))
        max_coefficient = float(np.max(np.abs(weights)))
        central = float(weights[2 * m - 1])
        u_abs = abs(float(data.u_coefficients[n]))
        rows.append(
            {
                "n": n,
                "m": m,
                "atom_count": int(k.size),
                "abs_u_n": f"{u_abs:.17g}",
                "block_l1_variation": f"{variation:.17g}",
                "max_abs_atom_coefficient": f"{max_coefficient:.17g}",
                "central_atom_coefficient": f"{central:.17g}",
                "variation_over_abs_u_n": (
                    f"{variation/u_abs:.17g}" if u_abs else "nan"
                ),
            }
        )
    return rows


def write_block_conditioning_table(
    output_path: Path, rows: Sequence[dict[str, object]]
) -> None:
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def make_figures(
    generated_dir: Path,
    data: SpectralData,
    conditioning_rows: Sequence[dict[str, object]],
) -> None:
    """Generate the report figures without selecting custom colors or styles."""
    import matplotlib.pyplot as plt
    import numpy as np

    generated_dir.mkdir(parents=True, exist_ok=True)

    # Figure 1: positive Legendre-energy contributions and the monotone
    # rational partial sums.  A long computed partial sum is shown as a
    # numerical reference, not asserted to be a proved closed form.
    terms = np.array(
        [
            float(u_n * u_n / Fraction(4 * n + 1))
            for n, u_n in enumerate(data.u_coefficients)
        ],
        dtype=np.float64,
    )
    partials = np.cumsum(terms)
    n_values = np.arange(len(terms))

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.semilogy(n_values[1:], terms[1:], marker="o", markersize=3, label=r"$u_n^2/(4n+1)$")
    ax.set_xlabel(r"Legendre block index $n$")
    ax.set_ylabel("positive energy contribution")
    ax.set_title("Positive rational Legendre-energy terms")
    ax.grid(True, which="both", linewidth=0.4)
    ax.legend()
    fig.tight_layout()
    fig.savefig(generated_dir / "energy_terms.pdf")
    fig.savefig(generated_dir / "energy_terms.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(n_values, partials, marker="o", markersize=2.5, label=r"$\sum_{j\leq N}u_j^2/(4j+1)$")
    ax.axhline(partials[-1], linestyle="--", label=f"N={len(partials)-1} reference")
    ax.set_xlabel(r"cutoff $N$")
    ax.set_ylabel(r"partial energy $A_{2,N}$")
    ax.set_title("Monotone exact-rational approximation to the Fabius square energy")
    ax.grid(True, linewidth=0.4)
    ax.legend()
    fig.tight_layout()
    fig.savefig(generated_dir / "energy_convergence.pdf")
    fig.savefig(generated_dir / "energy_convergence.png", dpi=180)
    plt.close(fig)

    # Figure 2: cancellation growth in the literal atom blocks.
    n = np.array([int(row["n"]) for row in conditioning_rows])
    variation = np.array(
        [float(row["block_l1_variation"]) for row in conditioning_rows]
    )
    maximum = np.array(
        [float(row["max_abs_atom_coefficient"]) for row in conditioning_rows]
    )
    mode_size = np.array([float(row["abs_u_n"]) for row in conditioning_rows])

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.semilogy(n, variation, marker="o", label=r"raw block variation $V_n$")
    ax.semilogy(n, maximum, marker="s", label="largest atom coefficient")
    ax.semilogy(n, mode_size, marker="^", label=r"resulting block size $|u_n|$")
    ax.set_xlabel(r"block index $n$")
    ax.set_ylabel("magnitude")
    ax.set_title("Internal cancellation in the exact Legendre--up blocks")
    ax.grid(True, which="both", linewidth=0.4)
    ax.legend()
    fig.tight_layout()
    fig.savefig(generated_dir / "block_cancellation_growth.pdf")
    fig.savefig(generated_dir / "block_cancellation_growth.png", dpi=180)
    plt.close(fig)

    # Figure 3: the explicit quarter-grid null stencil for Q_4.  The function
    # synthesized by these coefficients vanishes identically on [-1,1].
    q4 = data.q_polynomials[4]
    coarse_m = 16
    fine_m = 64
    k = np.arange(-2 * fine_m + 1, 2 * fine_m, dtype=np.int64)
    x = k.astype(np.float64) / float(fine_m)
    q_values = np.polynomial.polynomial.polyval(
        x, np.array([float(c) for c in q4], dtype=np.float64)
    )
    multipliers = np.where(k % 4 == 0, -3.0, 1.0)
    coefficients = multipliers * q_values / float(fine_m)

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(x, coefficients, marker=".", linewidth=0.8)
    ax.axhline(0.0, linewidth=0.8)
    ax.set_xlabel(r"fine-grid center $k/64$")
    ax.set_ylabel("null-train coefficient")
    ax.set_title(r"Quarter-grid null relation for $Q_4$: fine minus embedded coarse")
    ax.grid(True, linewidth=0.4)
    fig.tight_layout()
    fig.savefig(generated_dir / "quarter_grid_null_stencil.pdf")
    fig.savefig(generated_dir / "quarter_grid_null_stencil.png", dpi=180)
    plt.close(fig)


def write_summary(
    output_path: Path,
    synthesis_rows: Sequence[dict[str, object]],
    null_row: dict[str, object],
    lifting_row: dict[str, object],
    energy_rows: Sequence[dict[str, object]],
) -> None:
    """Write a concise human-readable verification transcript."""
    lines = [
        "Legendre--Rvachev exact verification summary",
        "=" * 48,
        "",
        "Finite Legendre synthesis checks:",
    ]
    for row in synthesis_rows:
        lines.append(
            f"  degree {row['degree']}: m={row['m']}, atoms={row['atom_count']}, "
            f"points={row['dyadic_points']}, residual={row['max_exact_residual']}"
        )
    lines.extend(
        [
            "",
            "Nested quarter-grid null relation:",
            f"  {null_row['polynomial']}, m={null_row['coarse_m']} -> {null_row['fine_m']}, "
            f"residual={null_row['max_exact_residual']}",
            "",
            "Fixed-scale lifting step:",
            f"  N={lifting_row['old_N']} -> {lifting_row['new_N']}, "
            f"coefficient residual={lifting_row['max_coefficient_residual']}, "
            f"functional residual={lifting_row['max_function_residual']}",
            "",
            "Positive rational energy checkpoints:",
        ]
    )
    for row in energy_rows:
        lines.append(
            f"  N={row['N']:>3}: A2_N={row['A2_partial_decimal']}, "
            f"last term={row['last_positive_term_decimal']}"
        )
    lines.extend(
        [
            "",
            "Every reported exact residual is the rational number 0.",
            "Floating-point calculations are confined to coefficient scans and plots.",
        ]
    )
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="artifact directory (default: directory containing this script)",
    )
    parser.add_argument(
        "--max-spectral-mode",
        type=int,
        default=100,
        help="largest n for exact u_n and energy calculations (default: 100)",
    )
    parser.add_argument(
        "--max-conditioning-mode",
        type=int,
        default=9,
        help="largest n for the full-grid floating coefficient scan (default: 9)",
    )
    parser.add_argument(
        "--no-plots",
        action="store_true",
        help="skip NumPy/Matplotlib figures",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = args.output_dir.resolve()
    data_dir = root / "data"
    generated_dir = root / "generated"
    data_dir.mkdir(parents=True, exist_ok=True)
    generated_dir.mkdir(parents=True, exist_ok=True)

    required_mode = max(args.max_spectral_mode, args.max_conditioning_mode, 3)
    table_mode = min(40, args.max_spectral_mode)
    required_q_degree = max(2 * table_mode, 2 * args.max_conditioning_mode, 6)
    spectral = build_spectral_data(required_mode, required_q_degree)

    synthesis_rows = verify_legendre_synthesis(
        data_dir / "exact_legendre_synthesis_checks.csv", max_degree=6
    )
    null_row = verify_nested_null_relation(
        data_dir / "exact_quarter_grid_null_check.csv"
    )
    lifting_row = verify_lifting_step(data_dir / "exact_lifting_check.csv")

    write_spectral_table(
        data_dir / "legendre_coefficients.csv",
        spectral,
        max_mode=min(40, args.max_spectral_mode),
    )
    checkpoints = [0, 1, 2, 4, 8, 16, 20, 30, 40, 60, 80, 100]
    checkpoints = [n for n in checkpoints if n <= args.max_spectral_mode]
    energy_rows = write_energy_table(
        data_dir / "positive_rational_energy.csv", spectral, checkpoints
    )

    conditioning_rows = block_conditioning_rows(
        spectral, args.max_conditioning_mode
    )
    write_block_conditioning_table(
        data_dir / "block_conditioning.csv", conditioning_rows
    )

    if not args.no_plots:
        make_figures(generated_dir, spectral, conditioning_rows)

    write_summary(
        data_dir / "verification_summary.txt",
        synthesis_rows,
        null_row,
        lifting_row,
        energy_rows,
    )

    print((data_dir / "verification_summary.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
