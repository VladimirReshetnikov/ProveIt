#!/usr/bin/env python3
"""Exact polynomial reproduction by translates/dilates of Rvachev's up function.

This script accompanies the report

    Exact Polynomial Plateaux from Rvachev's Up-Function

and implements its common-scale lattice construction in exact rational
arithmetic.  No floating-point approximation is used in the coefficients or in
the dyadic verification.  Floating point is used only for the optional plot.

Normalization
-------------
Let phi = up be the even compactly supported density on [-1,1], normalized by
integral(phi)=1 and

    phi_hat(xi) = product_{j>=0} sinc(pi*xi/2**j),

for the Fourier kernel exp(-2*pi*i*x*xi).  Its moment-generating function is

    M(z) = product_{j>=1} sinh(z/2**j)/(z/2**j).

For a positive integer m, define the up-Appell polynomials by

    sum_{r>=0} A_r^(m)(u) z^r/r! = exp(u*z)/(m*M(m*z)).

If r <= v_2(m), then the locally finite identity

    t^r = sum_{k in Z} A_r^(m)(k) phi((t-k)/m)

holds for every real t.  Compact support turns it into a finite identity after
restriction to a compact interval.

The exact dyadic evaluator uses the finite Thue--Morse/moment formula from the
ProveIt Fabius corpus.  It is independent of quadrature, FFTs, interpolation,
and sampled approximations.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence


def bernoulli_numbers(n: int) -> list[Fraction]:
    """Return B_0,...,B_n exactly by the Akiyama--Tanigawa algorithm.

    This implementation uses the +1/2 convention for B_1.  Only even-indexed
    Bernoulli numbers enter the up cumulants, so the B_1 convention is
    immaterial here.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    work = [Fraction(0) for _ in range(n + 1)]
    result: list[Fraction] = []
    for m in range(n + 1):
        work[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            work[j - 1] = j * (work[j - 1] - work[j])
        result.append(work[0])
    return result


def up_cumulants(max_order: int) -> list[Fraction]:
    r"""Return kappa_0,...,kappa_max_order for the up density.

    Odd cumulants vanish.  For r>=1,

        kappa_{2r} = 2^(2r-1) B_{2r} / (r (2^(2r)-1)).
    """
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
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
    """Convert cumulants to raw moments by the complete-Bell recurrence."""
    if not kappa:
        return []
    nmax = len(kappa) - 1
    mu = [Fraction(0) for _ in range(nmax + 1)]
    mu[0] = Fraction(1)
    for n in range(1, nmax + 1):
        mu[n] = sum(
            Fraction(math.comb(n - 1, j - 1)) * kappa[j] * mu[n - j]
            for j in range(1, n + 1)
        )
    return mu


def reciprocal_mgf_coefficients(m: int, max_order: int) -> list[Fraction]:
    r"""Return beta_n^(m) from 1/M(mz)=sum beta_n^(m) z^n/n!.

    Since M(mz)=sum m^j mu_j z^j/j!, multiplication of exponential generating
    functions gives the exact triangular recurrence

        beta_0 = 1,
        beta_n = -sum_{j=1}^n binom(n,j) m^j mu_j beta_{n-j}.
    """
    if m <= 0:
        raise ValueError("m must be positive")
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    mu = moments_from_cumulants(up_cumulants(max_order))
    beta = [Fraction(0) for _ in range(max_order + 1)]
    beta[0] = Fraction(1)
    for n in range(1, max_order + 1):
        beta[n] = -sum(
            Fraction(math.comb(n, j)) * (m**j) * mu[j] * beta[n - j]
            for j in range(1, n + 1)
        )
    return beta


def appell_value(
    r: int,
    m: int,
    u: int | Fraction,
    beta: Sequence[Fraction] | None = None,
) -> Fraction:
    r"""Evaluate A_r^(m)(u) exactly."""
    if r < 0:
        raise ValueError("r must be nonnegative")
    if beta is None:
        beta = reciprocal_mgf_coefficients(m, r)
    if len(beta) <= r:
        raise ValueError("beta table is too short")
    u = Fraction(u)
    return Fraction(1, m) * sum(
        Fraction(math.comb(r, j)) * u ** (r - j) * beta[j]
        for j in range(r + 1)
    )


def appell_polynomial_coefficients(r: int, m: int) -> list[Fraction]:
    """Return [a_0,...,a_r] for A_r^(m)(u)=sum a_j u^j."""
    beta = reciprocal_mgf_coefficients(m, r)
    result = [Fraction(0) for _ in range(r + 1)]
    for j in range(r + 1):
        result[r - j] += Fraction(math.comb(r, j), m) * beta[j]
    return result


def v2(n: int) -> int:
    """Return the 2-adic valuation of a positive integer."""
    if n <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (n & -n).bit_length() - 1


def floor_fraction(x: Fraction) -> int:
    """Exact floor of a Fraction."""
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    """Exact ceiling of a Fraction."""
    return -((-x.numerator) // x.denominator)


def polynomial_value(coefficients: Sequence[Fraction], x: Fraction) -> Fraction:
    """Evaluate sum_j coefficients[j] x^j by Horner's rule."""
    value = Fraction(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def affine_polynomial_coefficients(
    coefficients: Sequence[Fraction], x0: Fraction, h: Fraction
) -> list[Fraction]:
    r"""Return q_r for p(x0+h*t)=sum_r q_r t^r."""
    degree = len(coefficients) - 1
    q = [Fraction(0) for _ in range(degree + 1)]
    for r in range(degree + 1):
        q[r] = h**r * sum(
            coefficients[j] * math.comb(j, r) * x0 ** (j - r)
            for j in range(r, degree + 1)
        )
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return q


@dataclass(frozen=True)
class Representation:
    """A finite interval representation by common-scale up atoms."""

    polynomial: tuple[Fraction, ...]
    interval_left: Fraction
    interval_right: Fraction
    x0: Fraction
    h: Fraction
    m: int
    coefficients: tuple[tuple[int, Fraction], ...]

    @property
    def degree(self) -> int:
        return len(self.polynomial) - 1

    @property
    def atom_scale(self) -> Fraction:
        return self.m * self.h

    @property
    def index_min(self) -> int:
        return self.coefficients[0][0]

    @property
    def index_max(self) -> int:
        return self.coefficients[-1][0]


def construct_representation(
    polynomial: Sequence[Fraction],
    interval_left: Fraction,
    interval_right: Fraction,
    *,
    x0: Fraction = Fraction(0),
    h: Fraction = Fraction(1),
    m: int | None = None,
) -> Representation:
    r"""Construct the exact finite representation on [interval_left,right].

    ``polynomial[j]`` is the coefficient of x^j.  The returned formula is

        p(x) = sum_k c_k up((x-(x0+k*h))/(m*h))

    on the requested interval.  The canonical choice m=2^degree is used unless
    m is supplied.  A supplied m is accepted exactly when v_2(m)>=degree.
    """
    p = [Fraction(c) for c in polynomial]
    if not p:
        p = [Fraction(0)]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    degree = len(p) - 1
    interval_left = Fraction(interval_left)
    interval_right = Fraction(interval_right)
    x0 = Fraction(x0)
    h = Fraction(h)
    if interval_left > interval_right:
        raise ValueError("interval_left must not exceed interval_right")
    if h <= 0:
        raise ValueError("h must be positive")
    if m is None:
        m = 2**degree
    if m <= 0 or v2(m) < degree:
        raise ValueError(
            f"exact degree-{degree} reproduction requires v2(m) >= {degree}"
        )

    q = affine_polynomial_coefficients(p, x0, h)
    beta = reciprocal_mgf_coefficients(m, degree)
    k_min = ceil_fraction((interval_left - x0) / h - m)
    k_max = floor_fraction((interval_right - x0) / h + m)
    coefficients: list[tuple[int, Fraction]] = []
    for k in range(k_min, k_max + 1):
        coefficient = sum(
            q[r] * appell_value(r, m, k, beta) for r in range(len(q))
        )
        coefficients.append((k, coefficient))

    return Representation(
        polynomial=tuple(p),
        interval_left=interval_left,
        interval_right=interval_right,
        x0=x0,
        h=h,
        m=m,
        coefficients=tuple(coefficients),
    )


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
        moments = moments_from_cumulants(up_cumulants(n))
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
    denominator = (2 ** (n * (n + 1) // 2)) * math.factorial(n)
    return Fraction(total, denominator)


def up_dyadic(
    q: int, n: int, moments: Sequence[Fraction] | None = None
) -> Fraction:
    r"""Evaluate up(q/2^n) exactly, with up=0 at and outside +/-1."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if abs(q) >= 2**n:
        return Fraction(0)
    return fabius_dyadic(2**n - abs(q), n, moments)


def fraction_as_dyadic(x: Fraction) -> tuple[int, int]:
    """Return (q,n) with x=q/2^n; reject non-dyadic rationals."""
    x = Fraction(x)
    denominator = x.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"{x} is not dyadic")
    n = denominator.bit_length() - 1
    return x.numerator, n


def evaluate_representation_dyadic(rep: Representation, x: Fraction) -> Fraction:
    """Evaluate exactly when every atom argument is dyadic.

    In particular this holds when x, x0, h, and the atom scale are dyadic in a
    compatible way.  A non-dyadic argument is rejected rather than silently
    approximated.
    """
    arguments: list[tuple[Fraction, int, int]] = []
    max_n = 0
    for k, coefficient in rep.coefficients:
        argument = (Fraction(x) - (rep.x0 + k * rep.h)) / rep.atom_scale
        q, n = fraction_as_dyadic(argument)
        max_n = max(max_n, n)
        arguments.append((coefficient, q, n))
    moments = moments_from_cumulants(up_cumulants(max_n))
    return sum(
        coefficient * up_dyadic(q, n, moments)
        for coefficient, q, n in arguments
    )


def format_fraction(x: Fraction) -> str:
    """Canonical textual form for an exact fraction."""
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def write_appell_table(path: Path, max_degree: int, m: int) -> None:
    """Write all nonzero monomial coefficients of A_r^(m), r<=max_degree."""
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["degree", "power", "coefficient"])
        for r in range(max_degree + 1):
            for power, coefficient in enumerate(appell_polynomial_coefficients(r, m)):
                if coefficient:
                    writer.writerow([r, power, format_fraction(coefficient)])


def run_generic_degree_checks(
    output_dir: Path, max_degree: int = 6
) -> list[tuple[int, int, int, int, Fraction]]:
    """Run deterministic exact checks for degrees zero through max_degree.

    The physical atom radius is one.  Degree d uses the canonical m=2**d and
    h=1/m.  A nonzero lattice origin exercises the affine-coordinate path.
    """
    rows: list[tuple[int, int, int, int, Fraction]] = []
    for degree in range(max_degree + 1):
        polynomial = [
            Fraction(((-1) ** j) * (j + 2), j + 1)
            for j in range(degree + 1)
        ]
        m = 2**degree
        rep = construct_representation(
            polynomial,
            Fraction(-1, 4),
            Fraction(3, 4),
            x0=Fraction(3, 16),
            h=Fraction(1, m),
            m=m,
        )
        max_abs_residual = Fraction(0)
        point_count = 0
        for j in range(-4, 13):
            x = Fraction(j, 16)
            expected = polynomial_value(polynomial, x)
            actual = evaluate_representation_dyadic(rep, x)
            max_abs_residual = max(max_abs_residual, abs(actual - expected))
            point_count += 1
        if max_abs_residual != 0:
            raise AssertionError(
                f"generic degree-{degree} verification failed: {max_abs_residual}"
            )
        rows.append((degree, m, len(rep.coefficients), point_count, max_abs_residual))

    with (output_dir / "generic_degree_checks.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.writer(stream)
        writer.writerow(
            ["degree", "m", "atom_count", "dyadic_points", "max_exact_residual"]
        )
        for degree, m, atom_count, point_count, residual in rows:
            writer.writerow(
                [degree, m, atom_count, point_count, format_fraction(residual)]
            )
    return rows


def run_example(output_dir: Path, make_plot: bool = True) -> None:
    """Construct and verify the degree-four example used in the report."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # p(x)=7/5 - 3x + 2x^2 - x^3/2 + 3x^4/7 on [-1/2,3/2].
    polynomial = [
        Fraction(7, 5),
        Fraction(-3),
        Fraction(2),
        Fraction(-1, 2),
        Fraction(3, 7),
    ]
    rep = construct_representation(
        polynomial,
        Fraction(-1, 2),
        Fraction(3, 2),
        x0=Fraction(0),
        h=Fraction(1, 8),
        m=16,
    )

    with (output_dir / "example_coefficients.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.writer(stream)
        writer.writerow(["k", "center", "coefficient"])
        for k, coefficient in rep.coefficients:
            writer.writerow(
                [k, format_fraction(rep.x0 + k * rep.h), format_fraction(coefficient)]
            )

    rows: list[tuple[Fraction, Fraction, Fraction, Fraction]] = []
    max_abs_residual = Fraction(0)
    for j in range(-32, 97):  # 129 dyadic points, including both endpoints
        x = Fraction(j, 64)
        expected = polynomial_value(polynomial, x)
        actual = evaluate_representation_dyadic(rep, x)
        residual = actual - expected
        max_abs_residual = max(max_abs_residual, abs(residual))
        rows.append((x, expected, actual, residual))

    with (output_dir / "exact_grid_check.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.writer(stream)
        writer.writerow(["x", "polynomial", "up_sum", "residual"])
        for row in rows:
            writer.writerow([format_fraction(value) for value in row])

    write_appell_table(output_dir / "appell_coefficients_m16.csv", 8, 16)
    generic_rows = run_generic_degree_checks(output_dir, max_degree=6)

    summary = [
        "Exact Rvachev-up polynomial reproduction verification",
        "===================================================",
        f"degree: {rep.degree}",
        f"m: {rep.m} (v2(m)={v2(rep.m)})",
        f"h: {format_fraction(rep.h)}",
        f"atom scale m*h: {format_fraction(rep.atom_scale)}",
        f"index range: {rep.index_min}..{rep.index_max}",
        f"atom count: {len(rep.coefficients)}",
        f"dyadic verification points: {len(rows)}",
        f"maximum exact residual: {format_fraction(max_abs_residual)}",
        "generic degree checks: 0..6",
        f"generic checks passed: {sum(residual == 0 for *_, residual in generic_rows)}/{len(generic_rows)}",
    ]
    (output_dir / "verification_summary.txt").write_text(
        "\n".join(summary) + "\n", encoding="utf-8"
    )
    if max_abs_residual != 0:
        raise AssertionError(f"exact verification failed: {max_abs_residual}")

    if make_plot:
        try:
            import matplotlib.pyplot as plt
        except ImportError:
            return
        xs = [float(x) for x, _, _, _ in rows]
        ys = [float(y) for _, y, _, _ in rows]
        reconstructed = [float(y) for _, _, y, _ in rows]
        fig, ax = plt.subplots(figsize=(8.5, 4.8))
        ax.plot(xs, ys, linewidth=2.2, label="polynomial")
        ax.plot(
            xs,
            reconstructed,
            linestyle="--",
            linewidth=1.4,
            label="finite up-sum",
        )
        ax.set_xlabel("x")
        ax.set_ylabel("value")
        ax.set_title("Exact degree-four polynomial plateau (curves coincide)")
        ax.grid(True, alpha=0.25)
        ax.legend()
        fig.tight_layout()
        fig.savefig(output_dir / "representation_plot.png", dpi=180)
        plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for CSV, text, and PNG outputs",
    )
    parser.add_argument(
        "--no-plot", action="store_true", help="skip the optional matplotlib plot"
    )
    args = parser.parse_args()
    run_example(args.output_dir, make_plot=not args.no_plot)
    print(
        (args.output_dir / "verification_summary.txt").read_text(encoding="utf-8"),
        end="",
    )


if __name__ == "__main__":
    main()
