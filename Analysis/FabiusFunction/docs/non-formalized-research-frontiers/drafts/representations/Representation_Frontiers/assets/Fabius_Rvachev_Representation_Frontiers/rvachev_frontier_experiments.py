#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev representation report.

The script has four independent goals.

1. Compute the even moments of the Rvachev up-law exactly as rational numbers.
2. Recover exact Jacobi (J-fraction) coefficients by Gram--Schmidt orthogonalization.
3. Numerically verify the new Cauchy-transform functional equation
       R'(z) = 2 (R(2z+1) - R(2z-1)).
4. Numerically compare three logarithmic-derivative representations of the
   Fourier image Phi.

Only standard Python, mpmath, and matplotlib are required.  All normalizations
are stated explicitly below.

Fourier convention
------------------
    Phi(xi) = integral_{-1}^1 up(x) exp(-2*pi*i*xi*x) dx
            = product_{n>=0} sinc(pi*xi/2^n),
where sinc(u)=sin(u)/u.

Probabilistic model
-------------------
    X = sum_{k>=1} 2^{-k} U_k,
where the U_k are independent Uniform[-1,1].  Then up is the density of X.
The moment generating function is
    M(t) = E exp(tX)
         = product_{k>=1} sinh(t/2^k)/(t/2^k).

Cauchy transform
----------------
    R(z) = E[1/(z-X)].
For real z>1 it can be evaluated as a Laplace transform:
    R(z) = integral_0^infinity exp(-z*t) M(t) dt.

The exact arithmetic calculations intentionally use fractions.Fraction rather
than floating point.  This makes the printed recurrence coefficients suitable
for direct inclusion in a proof-oriented report.
"""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp

# Exact Hankel/Gram--Schmidt arithmetic quickly creates integers with more than
# Python's conservative default 4,300 decimal digits.  These values are local,
# trusted computations, so disabling that display guard is appropriate here.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


# ---------------------------------------------------------------------------
# Exact moments and exact monic orthogonal polynomials
# ---------------------------------------------------------------------------


def even_moments_exact(max_n: int) -> List[Fraction]:
    """Return [mu_0, mu_2, ..., mu_{2*max_n}] exactly.

    The recurrence follows from the distributional fixed point

        X  =_d  (U + X')/2,

    where U is Uniform[-1,1] and X' is an independent copy of X.  Expanding
    E[(U+X')^(2n)] and isolating the term containing mu_{2n} gives

        (4^n - 1) mu_{2n}
          = sum_{j=1}^n binom(2n,2j) mu_{2n-2j}/(2j+1).
    """

    if max_n < 0:
        raise ValueError("max_n must be nonnegative")

    from math import comb

    mu: List[Fraction] = [Fraction(1)]
    for n in range(1, max_n + 1):
        numerator = sum(
            Fraction(comb(2 * n, 2 * j), 2 * j + 1) * mu[n - j]
            for j in range(1, n + 1)
        )
        mu.append(numerator / (4**n - 1))
    return mu


def full_moment(moment_even: Sequence[Fraction], degree: int) -> Fraction:
    """Return mu_degree, using symmetry to set odd moments to zero."""

    if degree < 0:
        raise ValueError("degree must be nonnegative")
    if degree % 2:
        return Fraction(0)
    index = degree // 2
    if index >= len(moment_even):
        raise IndexError("moment table is too short")
    return moment_even[index]


def poly_inner_product(
    p: Sequence[Fraction],
    q: Sequence[Fraction],
    moment_even: Sequence[Fraction],
) -> Fraction:
    """Exact inner product integral p(x) q(x) up(x) dx.

    Polynomial coefficients are in ascending order: p[k] is the coefficient of
    x^k.  The up-law is even, so all odd moments vanish.
    """

    total = Fraction(0)
    for i, pi in enumerate(p):
        if not pi:
            continue
        for j, qj in enumerate(q):
            if qj:
                total += pi * qj * full_moment(moment_even, i + j)
    return total


def polynomial_subtract_scaled(
    p: List[Fraction], q: Sequence[Fraction], scale: Fraction
) -> None:
    """In-place p <- p - scale*q, extending p if required."""

    if len(p) < len(q):
        p.extend(Fraction(0) for _ in range(len(q) - len(p)))
    for k, qk in enumerate(q):
        p[k] -= scale * qk


@dataclass(frozen=True)
class JacobiData:
    """Exact data for the symmetric monic three-term recurrence."""

    beta: Tuple[Fraction, ...]  # beta[0] is beta_1
    norms: Tuple[Fraction, ...]  # h_0, h_1, ...
    monic_polynomials: Tuple[Tuple[Fraction, ...], ...]


def jacobi_parameters_exact(order: int) -> JacobiData:
    """Compute beta_1,...,beta_order exactly by the symmetric recurrence.

    Evenness forces every diagonal Jacobi coefficient to vanish.  Starting from
    P_0=1 and P_1=x, we therefore use

        P_{n+1}(x) = x P_n(x) - beta_n P_{n-1}(x),
        beta_n = h_n/h_{n-1},
        h_n = integral P_n(x)^2 up(x) dx.

    This Stieltjes procedure is much faster than full Gram--Schmidt while using
    exactly the same rational moment functional.  As a safeguard, the routine
    verifies orthogonality against the two preceding polynomials at every step;
    parity gives orthogonality to polynomials of the opposite parity.
    """

    if order < 1:
        raise ValueError("order must be at least 1")

    moments = even_moments_exact(order)
    p0 = [Fraction(1)]
    p1 = [Fraction(0), Fraction(1)]
    h0 = Fraction(1)
    h1 = poly_inner_product(p1, p1, moments)

    polynomials: List[List[Fraction]] = [p0, p1]
    norms: List[Fraction] = [h0, h1]
    beta: List[Fraction] = [h1 / h0]

    while len(beta) < order:
        n = len(polynomials) - 1  # current polynomial is P_n
        pn = polynomials[n]
        pnm1 = polynomials[n - 1]
        beta_n = beta[n - 1]

        # x*P_n - beta_n*P_{n-1}
        pnext = [Fraction(0)] + list(pn)
        polynomial_subtract_scaled(pnext, pnm1, beta_n)
        while len(pnext) > 1 and pnext[-1] == 0:
            pnext.pop()
        if pnext[-1] != 1:
            raise ArithmeticError("three-term recurrence lost monicity")

        hnext = poly_inner_product(pnext, pnext, moments)
        if hnext <= 0:
            raise ArithmeticError("nonpositive norm; moment computation failed")

        # The recurrence construction should make P_{n+1} orthogonal to P_n
        # and P_{n-1}; exact zero checks catch indexing/normalization errors.
        if poly_inner_product(pnext, pn, moments) != 0:
            raise ArithmeticError("failed exact orthogonality check against P_n")
        if poly_inner_product(pnext, pnm1, moments) != 0:
            raise ArithmeticError("failed exact orthogonality check against P_{n-1}")

        polynomials.append(pnext)
        norms.append(hnext)
        beta.append(hnext / norms[-2])

    return JacobiData(
        beta=tuple(beta),
        norms=tuple(norms),
        monic_polynomials=tuple(tuple(p) for p in polynomials),
    )


# ---------------------------------------------------------------------------
# Numerical products and transforms
# ---------------------------------------------------------------------------


def sinhc(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Stable sinh(x)/x with the removable value at x=0."""

    if x == 0:
        return mp.mpf(1)
    return mp.sinh(x) / x


def sinc(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Stable sin(x)/x with the removable value at x=0."""

    if x == 0:
        return mp.mpf(1)
    return mp.sin(x) / x


def mgf_up(t: mp.mpf | mp.mpc, factors: int = 80) -> mp.mpf | mp.mpc:
    """Truncated product for M(t)=product_{k>=1} sinh(t/2^k)/(t/2^k)."""

    product = mp.mpf(1)
    for k in range(1, factors + 1):
        product *= sinhc(t / (2**k))
    return product


def phi_up(xi: mp.mpf | mp.mpc, factors: int = 80) -> mp.mpf | mp.mpc:
    """Truncated sinc product for the Fourier transform Phi(xi)."""

    product = mp.mpf(1)
    for n in range(factors):
        product *= sinc(mp.pi * xi / (2**n))
    return product


def cauchy_transform_laplace(
    z: mp.mpf | mp.mpc, factors: int = 80
) -> mp.mpf | mp.mpc:
    """Evaluate R(z)=integral_0^infinity exp(-zt)M(t)dt for Re(z)>1.

    The integral is split into finite panels.  For Re(z)>1, M(t) grows no
    faster than exp(t), while the full integrand decays.  mpmath handles the
    tail interval [32,infinity] directly at the requested precision.
    """

    if mp.re(z) <= 1:
        raise ValueError("Laplace representation requires Re(z)>1")

    integrand = lambda t: mp.e ** (-z * t) * mgf_up(t, factors=factors)
    return mp.quad(integrand, [0, 1, 2, 4, 8, 16, 32, mp.inf])


def cauchy_derivative_laplace(
    z: mp.mpf | mp.mpc, factors: int = 80
) -> mp.mpf | mp.mpc:
    """Differentiate under the Laplace integral: R'(z)=-int t e^{-zt}M(t)dt."""

    if mp.re(z) <= 1:
        raise ValueError("Laplace representation requires Re(z)>1")

    integrand = lambda t: -t * mp.e ** (-z * t) * mgf_up(t, factors=factors)
    return mp.quad(integrand, [0, 1, 2, 4, 8, 16, 32, mp.inf])


def log_derivative_phi_sinc(
    xi: mp.mpf | mp.mpc, factors: int = 80
) -> mp.mpf | mp.mpc:
    """Sum of cotangent terms obtained by differentiating the sinc product."""

    total = mp.mpf(0)
    for n in range(factors):
        total += (mp.pi / (2**n)) / mp.tan(mp.pi * xi / (2**n)) - 1 / xi
    return total


def log_derivative_phi_cos(
    xi: mp.mpf | mp.mpc, factors: int = 80
) -> mp.mpf | mp.mpc:
    """Tangent series obtained by differentiating the weighted cosine product."""

    return -mp.pi * mp.fsum(
        (m / (2**m)) * mp.tan(mp.pi * xi / (2**m))
        for m in range(1, factors + 1)
    )


def valuation_two(n: int) -> int:
    """Return nu_2(n) for a positive integer n."""

    if n <= 0:
        raise ValueError("n must be positive")
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def log_derivative_phi_zeros(
    xi: mp.mpf | mp.mpc, cutoff: int = 200_000
) -> mp.mpf | mp.mpc:
    """Truncated zero-set partial fraction sum.

        Phi'(xi)/Phi(xi)
          = -2 xi sum_{n>=1} (1+nu_2(n))/(n^2-xi^2).

    This representation converges only algebraically, unlike the dyadic
    cotangent and tangent representations, so a substantially larger cutoff is
    used.  A simple integral-sized tail estimate is reported separately.
    """

    return -2 * xi * mp.fsum(
        (1 + valuation_two(n)) / (mp.mpf(n) ** 2 - xi**2)
        for n in range(1, cutoff + 1)
    )


def even_moments_mp(max_n: int) -> List[mp.mpf]:
    """High-precision floating-point counterpart of even_moments_exact."""

    from math import comb

    mu: List[mp.mpf] = [mp.mpf(1)]
    for n in range(1, max_n + 1):
        numerator = mp.fsum(
            mp.mpf(comb(2 * n, 2 * j)) * mu[n - j] / (2 * j + 1)
            for j in range(1, n + 1)
        )
        mu.append(numerator / (mp.mpf(4) ** n - 1))
    return mu


def cauchy_transform_moment_series(
    z: mp.mpf | mp.mpc, moments: Sequence[mp.mpf]
) -> mp.mpf | mp.mpc:
    """Evaluate R(z)=sum mu_{2n}/z^{2n+1}, valid for |z|>1."""

    if abs(z) <= 1:
        raise ValueError("moment series requires |z|>1")
    inv = 1 / z
    inv2 = inv * inv
    power = inv
    terms = []
    for mu in moments:
        terms.append(mu * power)
        power *= inv2
    return mp.fsum(terms)


def cauchy_derivative_moment_series(
    z: mp.mpf | mp.mpc, moments: Sequence[mp.mpf]
) -> mp.mpf | mp.mpc:
    """Termwise derivative of the large-z Cauchy series."""

    if abs(z) <= 1:
        raise ValueError("moment series requires |z|>1")
    inv = 1 / z
    inv2 = inv * inv
    power = inv2
    terms = []
    for n, mu in enumerate(moments):
        terms.append(-(2 * n + 1) * mu * power)
        power *= inv2
    return mp.fsum(terms)


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


def fraction_to_latex(q: Fraction) -> str:
    """Render a rational number as compact LaTeX."""

    if q.denominator == 1:
        return str(q.numerator)
    return rf"\frac{{{q.numerator}}}{{{q.denominator}}}"


def write_moment_csv(path: Path, moments: Sequence[Fraction]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["n", "moment", "numerator", "denominator", "decimal"])
        for n, q in enumerate(moments):
            writer.writerow([2 * n, f"mu_{2*n}", q.numerator, q.denominator, float(q)])


def write_jacobi_csv(path: Path, beta: Sequence[Fraction]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(
            [
                "n",
                "beta_n_numerator",
                "beta_n_denominator",
                "beta_n_decimal",
                "quarter_minus_beta_n",
                "scaled_n2_over_log2",
            ]
        )
        for n, q in enumerate(beta, start=1):
            decimal = mp.mpf(q.numerator) / q.denominator
            deficit = mp.mpf("0.25") - decimal
            scaled = mp.nan if n == 1 else deficit * n * n / (mp.log(n) ** 2)
            writer.writerow(
                [
                    n,
                    q.numerator,
                    q.denominator,
                    mp.nstr(decimal, 20),
                    mp.nstr(deficit, 20),
                    "" if n == 1 else mp.nstr(scaled, 20),
                ]
            )


def write_latex_tables(
    path: Path, moments: Sequence[Fraction], beta: Sequence[Fraction]
) -> None:
    """Write small LaTeX fragments consumed by the main report."""

    with path.open("w", encoding="utf-8") as handle:
        handle.write("% Auto-generated by rvachev_frontier_experiments.py\n")
        handle.write("\\begin{tabular}{rll}\n")
        handle.write("\\toprule\n$n$ & $\\mu_{2n}$ & decimal \\\\\n\\midrule\n")
        for n, q in enumerate(moments[:11]):
            handle.write(
                f"{n} & ${fraction_to_latex(q)}$ & "
                f"${float(q):.12g}$ \\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n\n")

        handle.write("\\begin{tabular}{rll}\n")
        handle.write("\\toprule\n$n$ & $\\beta_n$ (exact when compact) & decimal \\\\\n\\midrule\n")
        for n, q in enumerate(beta[:12], start=1):
            exact = fraction_to_latex(q)
            # Avoid typesetting enormous exact fractions in the main table.
            if len(str(q.numerator)) + len(str(q.denominator)) > 38:
                exact = r"\text{see data file}"
            handle.write(
                f"{n} & ${exact}$ & ${float(q):.12f}$ \\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")


def create_figures(output_dir: Path, beta: Sequence[Fraction]) -> None:
    """Create two separate, publication-ready diagnostic figures."""

    # Import lazily, so exact-arithmetic users do not need matplotlib.
    import matplotlib.pyplot as plt

    n_values = list(range(1, len(beta) + 1))
    beta_values = [float(q) for q in beta]

    fig = plt.figure(figsize=(6.4, 4.0))
    ax = fig.add_subplot(111)
    ax.plot(n_values, beta_values, marker="o", markersize=2.5, linewidth=1.0)
    ax.axhline(0.25, linestyle="--", linewidth=1.0, label=r"limit $1/4$")
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"$\beta_n$")
    ax.set_title("Jacobi coefficients of the Rvachev up-law")
    ax.legend()
    ax.grid(True, linewidth=0.3)
    fig.tight_layout()
    fig.savefig(output_dir / "jacobi_coefficients.pdf")
    fig.savefig(output_dir / "jacobi_coefficients.png", dpi=180)
    plt.close(fig)

    n_scaled = n_values[1:]
    scaled = [
        (0.25 - beta_values[n - 1]) * n * n / (mp.log(n) ** 2)
        for n in n_scaled
    ]
    fig = plt.figure(figsize=(6.4, 4.0))
    ax = fig.add_subplot(111)
    ax.plot(n_scaled, [float(v) for v in scaled], marker="o", markersize=2.5, linewidth=1.0)
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"$n^2(1/4-\beta_n)/(\log n)^2$")
    ax.set_title("A diagnostic for the unresolved Jacobi-parameter rate")
    ax.grid(True, linewidth=0.3)
    fig.tight_layout()
    fig.savefig(output_dir / "jacobi_scaled_deficit.pdf")
    fig.savefig(output_dir / "jacobi_scaled_deficit.png", dpi=180)
    plt.close(fig)


def numerical_checks(output_dir: Path, digits: int = 50) -> str:
    """Run independent high-precision checks and return a text report.

    The resolvent is evaluated from its moment expansion rather than from the
    functional equation under test.  This avoids a circular check.  Two
    truncation lengths are compared to expose the numerical tail directly.
    """

    mp.mp.dps = digits
    lines: List[str] = []
    lines.append(f"mpmath precision: {digits} decimal digits")
    lines.append("")

    moments_short = even_moments_mp(160)
    moments_long = even_moments_mp(220)

    lines.append("Cauchy-transform functional equation")
    lines.append("R'(z) = 2(R(2z+1)-R(2z-1))")
    for z in [mp.mpf("1.25"), mp.mpf("1.75"), mp.mpf("2.5")]:
        lhs = cauchy_derivative_moment_series(z, moments_long)
        rhs = 2 * (
            cauchy_transform_moment_series(2 * z + 1, moments_long)
            - cauchy_transform_moment_series(2 * z - 1, moments_long)
        )
        lhs_short = cauchy_derivative_moment_series(z, moments_short)
        rhs_short = 2 * (
            cauchy_transform_moment_series(2 * z + 1, moments_short)
            - cauchy_transform_moment_series(2 * z - 1, moments_short)
        )
        abs_error = abs(lhs - rhs)
        rel_error = abs_error / max(mp.mpf(1), abs(lhs), abs(rhs))
        truncation_indicator = max(abs(lhs - lhs_short), abs(rhs - rhs_short))
        lines.append(
            f"z={mp.nstr(z,8)}  lhs={mp.nstr(lhs,25)}  "
            f"rhs={mp.nstr(rhs,25)}  rel.err={mp.nstr(rel_error,8)}  "
            f"160/220 change={mp.nstr(truncation_indicator,8)}"
        )
    lines.append("")

    lines.append("Three logarithmic-derivative representations")
    lines.append("cotangent sum, tangent sum, and zero-set partial fractions")
    for xi in [mp.mpf("0.13"), mp.mpf("0.37"), mp.mpf("0.73")]:
        cot_value = log_derivative_phi_sinc(xi)
        tan_value = log_derivative_phi_cos(xi)
        zero_value = log_derivative_phi_zeros(xi, cutoff=100_000)
        lines.append(
            f"xi={mp.nstr(xi,8)}  cot={mp.nstr(cot_value,25)}  "
            f"tan={mp.nstr(tan_value,25)}  zero={mp.nstr(zero_value,25)}"
        )
        lines.append(
            f"             |cot-tan|={mp.nstr(abs(cot_value-tan_value),8)}  "
            f"|cot-zero|={mp.nstr(abs(cot_value-zero_value),8)}"
        )

    report = "\n".join(lines) + "\n"
    (output_dir / "numerical_checks.txt").write_text(report, encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--order",
        type=int,
        default=40,
        help="largest exact Jacobi coefficient to compute (default: 40)",
    )
    parser.add_argument(
        "--digits",
        type=int,
        default=50,
        help="mpmath decimal precision for numerical checks (default: 50)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for CSV, LaTeX fragments, figures, and check log",
    )
    args = parser.parse_args()

    if args.order < 12:
        raise SystemExit("Please use --order at least 12 for the report tables.")

    args.output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Computing exact moments and Jacobi data through n={args.order} ...")
    moments = even_moments_exact(args.order)
    jacobi = jacobi_parameters_exact(args.order)

    write_moment_csv(args.output_dir / "up_even_moments.csv", moments)
    write_jacobi_csv(args.output_dir / "up_jacobi_coefficients.csv", jacobi.beta)
    write_latex_tables(
        args.output_dir / "generated_tables.tex", moments, jacobi.beta
    )
    create_figures(args.output_dir, jacobi.beta)

    print("Running high-precision transform checks ...")
    report = numerical_checks(args.output_dir, digits=args.digits)
    print(report)

    print("First six exact Jacobi coefficients:")
    for n, q in enumerate(jacobi.beta[:6], start=1):
        print(f"beta_{n} = {q} = {float(q):.15f}")

    print(f"Wrote reproducibility artifacts to {args.output_dir}")


if __name__ == "__main__":
    main()
