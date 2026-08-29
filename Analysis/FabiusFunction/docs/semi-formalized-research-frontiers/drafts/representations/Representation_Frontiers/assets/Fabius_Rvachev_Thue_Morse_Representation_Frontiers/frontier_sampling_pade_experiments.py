#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev--Thue--Morse report.

The program verifies and illustrates four theorem families developed in the
accompanying LaTeX report:

1. sparse half-lattice Shannon sampling and the associated Mittag--Leffler
   expansion of the Rvachev Fourier image Phi;
2. the cosine series for up and F, including weighted Thue--Morse moment
   cancellations at the flat point;
3. the formal orthogonal-polynomial/Jacobi-fraction structure of the signed
   Thue--Morse moment functional, including the exact dyadic Pade denominator
   1+z^(2^m) and its complex Gaussian quadrature;
4. Mellin identities and the Bose--Malmsten product-integral representation.

All exact algebra uses fractions.Fraction.  High-precision numerical work uses
mpmath.  Matplotlib is needed only for the optional figures.  No data are fitted
and then inserted into proofs: the script checks identities proved separately
in the report and supplies evidence only for explicitly labelled conjectures.

Usage:
    python frontier_sampling_pade_experiments.py --output-dir output

Dependencies:
    Python >= 3.10, mpmath, scipy, matplotlib
"""

from __future__ import annotations

import argparse
import cmath
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp


# ---------------------------------------------------------------------------
# Elementary Thue--Morse and polynomial utilities
# ---------------------------------------------------------------------------


def thue_morse_sign(n: int) -> int:
    """Return epsilon_n=(-1)^s_2(n), where s_2 is the binary digit sum."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


def thue_morse_bit(n: int) -> int:
    """Return tau_n=s_2(n) mod 2 in {0,1}."""
    return (1 - thue_morse_sign(n)) // 2


def finite_tm_polynomial_value(m: int, z: complex | mp.mpf | mp.mpc) -> complex | mp.mpf | mp.mpc:
    """P_m(z)=prod_{j<m}(1-z^(2^j))=sum_{n<2^m} epsilon_n z^n."""
    value = mp.mpf(1)
    for j in range(m):
        value *= 1 - z ** (1 << j)
    return value


def signed_tm_ogf(z: complex | mp.mpf | mp.mpc, terms: int = 80) -> complex | mp.mpf | mp.mpc:
    """Evaluate E(z)=prod_{j>=0}(1-z^(2^j)) for |z|<1.

    The lacunary exponents make direct product evaluation extremely fast.
    ``terms`` is a hard safety cap; the loop normally exits much sooner.
    """
    if abs(z) >= 1:
        raise ValueError("signed_tm_ogf requires |z|<1")
    value = mp.mpf(1)
    power = z
    for _ in range(terms):
        value *= 1 - power
        if abs(power) < mp.eps:
            break
        power *= power
    return value


# ---------------------------------------------------------------------------
# Rvachev Fourier image Phi and half-lattice coefficients
# ---------------------------------------------------------------------------


def sinc_pi(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Normalized sinc sin(pi*z)/(pi*z), with its removable value at zero."""
    if z == 0:
        return mp.mpf(1)
    return mp.sin(mp.pi * z) / (mp.pi * z)


def phi(z: mp.mpf | mp.mpc, max_terms: int = 400) -> mp.mpf | mp.mpc:
    r"""Compute Phi(z)=prod_{j>=0} sinc_pi(z/2^j).

    For bounded z, once |z|/2^j is tiny the omitted logarithmic tail is
    O(|z|^2 4^{-j}); the stopping test is therefore based on that quantity.
    """
    z = mp.mpc(z) if isinstance(z, complex) or getattr(z, "imag", 0) else mp.mpf(z)
    value = mp.mpf(1)
    scale = z
    for j in range(max_terms):
        value *= sinc_pi(scale)
        scale /= 2
        if abs(scale) ** 2 < mp.eps / 10:
            break
    else:
        raise RuntimeError("phi product did not converge within max_terms")
    return value


def half_lattice_coefficient(k: int) -> mp.mpf:
    """c_k=Phi(k+1/2), evaluated by a sign-stable logarithmic product."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    z = mp.mpf(k) + mp.mpf("0.5")
    log_abs = mp.mpf(0)
    scale = z
    sign = 1
    for _ in range(500):
        factor = sinc_pi(scale)
        if factor == 0:
            return mp.mpf(0)
        if factor < 0:
            sign = -sign
        log_abs += mp.log(abs(factor))
        scale /= 2
        if scale ** 2 < mp.eps / 10:
            break
    value = mp.mpf(sign) * mp.exp(log_abs)
    # The exact sign theorem is epsilon_k.  Failing here signals either a
    # numerical problem or a normalization mismatch.
    if mp.sign(value) != thue_morse_sign(k):
        raise ArithmeticError(f"half-lattice sign mismatch at k={k}")
    return value


def sparse_sampling_phi(z: mp.mpf | mp.mpc, coeffs: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    r"""Truncated sparse Shannon series.

    Phi(z)=sinc_pi(2z)+sum_{k>=0} c_k[sinc_pi(2z-a_k)+sinc_pi(2z+a_k)],
    a_k=2k+1.
    """
    total = sinc_pi(2 * z)
    for k, ck in enumerate(coeffs):
        a = 2 * k + 1
        total += ck * (sinc_pi(2 * z - a) + sinc_pi(2 * z + a))
    return total


def mittag_leffler_phi_ratio(z: mp.mpf | mp.mpc, coeffs: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    r"""Truncated partial-fraction formula for pi*Phi(z)/sin(2*pi*z)."""
    total = 1 / (2 * z)
    for k, ck in enumerate(coeffs):
        a = 2 * k + 1
        total -= 4 * z * ck / (4 * z * z - a * a)
    return total


# ---------------------------------------------------------------------------
# Finite convolution spline, independent check of the cosine series
# ---------------------------------------------------------------------------


def finite_up_spline(x: mp.mpf, depth: int) -> mp.mpf:
    r"""Density of X_depth=sum_{k=1}^depth 2^{-k} U_k, U_k~Unif[-1,1].

    Inclusion--exclusion gives the compactly supported spline

      rho_N(x)=2^{N(N-1)/2}/(N-1)! *
               sum_{r<2^N} epsilon_r
               (x+1-2^{-N}-r/2^{N-1})_+^{N-1}.

    This is expensive in N but is an independent real-space check for N<=14.
    """
    if depth < 1:
        raise ValueError("depth must be at least 1")
    N = depth
    shift = mp.mpf(1) - mp.power(2, -N)
    grid = mp.power(2, N - 1)
    prefactor = mp.power(2, N * (N - 1) // 2) / mp.factorial(N - 1)
    total = mp.mpf(0)
    for r in range(1 << N):
        y = x + shift - mp.mpf(r) / grid
        if y > 0:
            total += thue_morse_sign(r) * y ** (N - 1)
    return prefactor * total


def cosine_up(x: mp.mpf, coeffs: Sequence[mp.mpf]) -> mp.mpf:
    """Truncated sparse cosine series rho(x)=1/2+sum c_k cos((2k+1)pi x)."""
    total = mp.mpf("0.5")
    for k, ck in enumerate(coeffs):
        total += ck * mp.cos((2 * k + 1) * mp.pi * x)
    return total


# ---------------------------------------------------------------------------
# Formal orthogonal polynomials for L[x^n]=epsilon_n
# ---------------------------------------------------------------------------

Polynomial = list[Fraction]  # ascending coefficient order


def poly_trim(p: Polynomial) -> Polynomial:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_x_minus_a(p: Polynomial, a: Fraction) -> Polynomial:
    out = [Fraction(0)] * (len(p) + 1)
    for i, c in enumerate(p):
        out[i + 1] += c
        out[i] -= a * c
    return poly_trim(out)


def poly_sub_scaled(p: Polynomial, q: Polynomial, scale: Fraction) -> Polynomial:
    out = [Fraction(0)] * max(len(p), len(q))
    for i, c in enumerate(p):
        out[i] += c
    for i, c in enumerate(q):
        out[i] -= scale * c
    return poly_trim(out)


def formal_inner(p: Polynomial, q: Polynomial, shift: int = 0) -> Fraction:
    """L[x^shift p(x)q(x)] for L[x^n]=epsilon_n."""
    total = Fraction(0)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            if b:
                total += a * b * thue_morse_sign(i + j + shift)
    return total


@dataclass
class FormalJacobiData:
    polynomials: list[Polynomial]
    norms: list[Fraction]
    diagonal: list[Fraction]
    subdiagonal: list[Fraction | None]


def formal_jacobi_data(max_degree: int) -> FormalJacobiData:
    """Exact monic Gram--Schmidt/Jacobi data through ``max_degree``.

    p_{n+1}=(x-a_n)p_n-b_n p_{n-1}, p_{-1}=0, p_0=1.
    The Thue--Morse Hankel determinants are nonzero, so no division by zero
    occurs.  Fractions are retained exactly.
    """
    polynomials: list[Polynomial] = [[Fraction(1)]]
    norms: list[Fraction] = [Fraction(1)]
    diagonal: list[Fraction] = []
    subdiagonal: list[Fraction | None] = [None]

    for n in range(max_degree):
        p_n = polynomials[n]
        h_n = norms[n]
        a_n = formal_inner(p_n, p_n, shift=1) / h_n
        diagonal.append(a_n)
        if n == 0:
            b_n = Fraction(0)
        else:
            b_n = h_n / norms[n - 1]
            subdiagonal.append(b_n)

        p_next = poly_x_minus_a(p_n, a_n)
        if n > 0:
            p_next = poly_sub_scaled(p_next, polynomials[n - 1], b_n)
        polynomials.append(p_next)
        norms.append(formal_inner(p_next, p_next))

    return FormalJacobiData(polynomials, norms, diagonal, subdiagonal)


def expected_b_from_dyadic_recursion(max_index: int) -> list[Fraction | None]:
    r"""Generate b_n from the proved nonlinear dyadic recursion.

    b_1=-2,
    b_{2n}=b_n/b_{2n-1},
    b_{2n+1}=(-1)^{n+1}-1-b_{2n}.
    """
    if max_index < 1:
        return [None]
    b: list[Fraction | None] = [None] * (max_index + 1)
    b[1] = Fraction(-2)
    n = 1
    while 2 * n <= max_index:
        assert b[n] is not None and b[2 * n - 1] is not None
        b[2 * n] = b[n] / b[2 * n - 1]
        if 2 * n + 1 <= max_index:
            a_n = Fraction(-1 if n % 2 == 0 else 1)
            b[2 * n + 1] = a_n - 1 - b[2 * n]
        n += 1
    return b


# ---------------------------------------------------------------------------
# Pade approximants and antiperiodic complex quadrature
# ---------------------------------------------------------------------------


def dyadic_pade(m: int, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """[2^m-1 / 2^m] Pade approximant P_m(z)/(1+z^(2^m))."""
    N = 1 << m
    return finite_tm_polynomial_value(m, z) / (1 + z ** N)


def antiperiodic_quadrature(m: int, r: int) -> mp.mpc:
    r"""N-node complex quadrature sum reproducing epsilon_r for r<2N.

    lambda_j=exp((2j+1)pi*i/N), lambda_j^N=-1,
    w_j=P_m(lambda_j^{-1})/N,
    epsilon_r=sum_j w_j lambda_j^r.
    """
    N = 1 << m
    total = mp.mpc(0)
    for j in range(N):
        lam = mp.e ** (mp.j * mp.pi * (2 * j + 1) / N)
        weight = finite_tm_polynomial_value(m, 1 / lam) / N
        total += weight * lam ** r
    return total


# ---------------------------------------------------------------------------
# Exact moments and Mellin transforms
# ---------------------------------------------------------------------------


def exact_up_moments(max_order: int) -> list[Fraction]:
    r"""Moments mu_n=E[X^n] of X=sum 2^{-k}U_k, U_k~Unif[-1,1].

    From X=(U+X')/2 with X' distributed as X,

      (2^n-1)mu_n=sum_{j<n} binom(n,j) E[U^{n-j}] mu_j.

    Odd moments vanish.  The recurrence uses exact rational arithmetic.
    """
    mu = [Fraction(0)] * (max_order + 1)
    mu[0] = Fraction(1)
    for n in range(1, max_order + 1):
        total = Fraction(0)
        for j in range(n):
            power = n - j
            if power % 2 == 0:
                uniform_moment = Fraction(1, power + 1)
                total += Fraction(math.comb(n, j)) * uniform_moment * mu[j]
        mu[n] = total / (2**n - 1)
    return mu


def generalized_binomial(s: mp.mpf | mp.mpc, n: int) -> mp.mpf | mp.mpc:
    return mp.binomial(s, n)


def mellin_y_series(s: mp.mpf | mp.mpc, moments: Sequence[Fraction]) -> mp.mpf | mp.mpc:
    r"""M_Y(s)=E[((1+X)/2)^s] from its even-moment binomial series.

    Absolute convergence is guaranteed for Re(s)>0.  A finite moment list gives
    a controlled truncation for the numerical checks below.
    """
    total = mp.mpc(0)
    for j in range(0, len(moments), 2):
        q = moments[j]
        total += generalized_binomial(s, j) * mp.mpf(q.numerator) / q.denominator
    return mp.power(2, -s) * total


def mellin_y_from_cosine(
    s: mp.mpf | mp.mpc, coeffs: Sequence[mp.mpf]
) -> mp.mpc:
    """Independent quadrature of E[Y^s] from the sparse cosine density.

    The theorem gives the density of Y=(1+X)/2 as

        f_Y(y)=1+2*sum_k c_k cos((2k+1)pi(2y-1)).

    For the numerical check we integrate this representation with SciPy's
    adaptive Gauss--Kronrod quadrature.  Only double precision is needed here;
    the high-precision moment series remains the reference computation.
    """
    from scipy.integrate import quad

    s_complex = complex(s)
    coeff_float = [float(c) for c in coeffs if abs(c) > mp.mpf("1e-40")]

    def density(y: float) -> float:
        x = 2.0 * y - 1.0
        total = 1.0
        for k, ck in enumerate(coeff_float):
            total += 2.0 * ck * math.cos((2 * k + 1) * math.pi * x)
        return total

    def integrand(y: float) -> complex:
        if y == 0.0:
            return 0.0j
        return cmath.exp(s_complex * math.log(y)) * density(y)

    real = quad(lambda y: integrand(y).real, 0.0, 1.0, epsabs=2e-13, epsrel=2e-13, limit=300)[0]
    imag = quad(lambda y: integrand(y).imag, 0.0, 1.0, epsabs=2e-13, epsrel=2e-13, limit=300)[0]
    return mp.mpc(real, imag)


# ---------------------------------------------------------------------------
# Bose--Malmsten integral for log Phi
# ---------------------------------------------------------------------------


def dyadic_cosh_kernel(u: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """H(u)=sum_{j>=0}(cosh(u/2^j)-1), evaluated directly."""
    total = mp.mpc(0)
    scale = u
    for _ in range(500):
        term = mp.cosh(scale) - 1
        total += term
        scale /= 2
        if abs(term) < mp.eps * max(1, abs(total)):
            break
    return total


def log_phi_malmsten(z: mp.mpf | mp.mpc) -> mp.mpc:
    r"""Numerically integrate the Malmsten formula in |Re z|<1.

      log Phi(z)=-2 int_0^infty H(zt)/(t(e^t-1)) dt.

    A double-precision Gauss--Kronrod integral is deliberately used as an
    implementation independent of the high-precision infinite product.  The
    tail beyond T=80 is exponentially tiny for the test points below.
    """
    from scipy.integrate import quad

    zc = complex(z)
    if abs(zc.real) >= 1:
        raise ValueError("Malmsten integral implemented only for |Re(z)|<1")

    def kernel(u: complex) -> complex:
        total = 0.0j
        scale = u
        for _ in range(120):
            # 2*sinh(u/2)^2 is more stable than cosh(u)-1 near the origin.
            term = 2.0 * cmath.sinh(scale / 2.0) ** 2
            total += term
            scale /= 2.0
            if abs(term) < 1e-17 * max(1.0, abs(total)):
                break
        return total

    def integrand(t: float) -> complex:
        if t == 0.0:
            return 0.0j
        return -2.0 * kernel(zc * t) / (t * math.expm1(t))

    intervals = [(0.0, 1.0), (1.0, 4.0), (4.0, 12.0), (12.0, 30.0), (30.0, 80.0)]
    real = sum(
        quad(lambda t: integrand(t).real, a, b, epsabs=2e-13, epsrel=2e-13, limit=300)[0]
        for a, b in intervals
    )
    imag = sum(
        quad(lambda t: integrand(t).imag, a, b, epsabs=2e-13, epsrel=2e-13, limit=300)[0]
        for a, b in intervals
    )
    return mp.mpc(real, imag)


# ---------------------------------------------------------------------------
# Output and plots
# ---------------------------------------------------------------------------


def fraction_string(q: Fraction | None) -> str:
    if q is None:
        return ""
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def write_text(path: Path, lines: Iterable[str]) -> None:
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def generate_all(output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    data_dir = output_dir / "data"
    fig_dir = output_dir / "figures"
    data_dir.mkdir(exist_ok=True)
    fig_dir.mkdir(exist_ok=True)

    mp.mp.dps = 80

    # Half-lattice coefficients.
    coeffs = [half_lattice_coefficient(k) for k in range(128)]
    with (data_dir / "half_lattice_coefficients.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["k", "epsilon_k", "tau_k", "c_k=Phi(k+1/2)", "-log_abs_c_k"])
        for k, ck in enumerate(coeffs):
            writer.writerow([
                k,
                thue_morse_sign(k),
                thue_morse_bit(k),
                mp.nstr(ck, 45),
                mp.nstr(-mp.log(abs(ck)), 35),
            ])

    # Sampling, Mittag--Leffler, and cosine-series checks.
    check_lines = [
        "Sparse half-lattice sampling and Mittag--Leffler checks",
        f"mpmath decimal precision: {mp.mp.dps}",
        "",
    ]
    test_points = [
        mp.mpf("0.137"),
        mp.mpf("0.731"),
        mp.mpf("1.2345"),
        mp.mpc("0.37", "0.22"),
        mp.mpc("-0.41", "0.31"),
    ]
    for z in test_points:
        direct = phi(z)
        sampled = sparse_sampling_phi(z, coeffs)
        check_lines.append(
            f"z={mp.nstr(z,12):>18}  |Phi-sampling|={mp.nstr(abs(direct-sampled),8)}"
        )
        if abs(mp.sin(2 * mp.pi * z)) > mp.mpf("1e-30") and z != 0:
            direct_ratio = mp.pi * direct / mp.sin(2 * mp.pi * z)
            partial_fraction = mittag_leffler_phi_ratio(z, coeffs)
            check_lines.append(
                f"{'':>22}  |ratio-ML|={mp.nstr(abs(direct_ratio-partial_fraction),8)}"
            )
    check_lines.append("")
    check_lines.append("Cosine series versus independent finite convolution spline (depth 13):")
    for x in [mp.mpf("0"), mp.mpf("0.125"), mp.mpf("0.25"), mp.mpf("0.375"), mp.mpf("0.7")]:
        series = cosine_up(x, coeffs)
        spline = finite_up_spline(x, 13)
        check_lines.append(
            f"x={mp.nstr(x,8):>8}  series={mp.nstr(series,18):>22}  "
            f"spline={mp.nstr(spline,18):>22}  diff={mp.nstr(abs(series-spline),8)}"
        )
    write_text(data_dir / "sampling_checks.txt", check_lines)

    # Weighted flatness cancellations.
    cancellation_rows: list[list[str | int]] = []
    for K in [4, 8, 12, 16, 24, 32, 48, 64, 96, 128]:
        for r in range(0, 5):
            value = mp.fsum(coeffs[k] * (2 * k + 1) ** (2 * r) for k in range(K))
            target = mp.mpf("0.5") if r == 0 else mp.mpf(0)
            cancellation_rows.append([K, r, mp.nstr(value, 40), mp.nstr(abs(value - target), 30)])
    with (data_dir / "weighted_cancellations.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["truncation_K", "r", "partial_sum", "absolute_error"])
        writer.writerows(cancellation_rows)

    # Exact formal Jacobi data and proof checks.
    max_degree = 96
    jacobi = formal_jacobi_data(max_degree)
    recursive_b = expected_b_from_dyadic_recursion(max_degree - 1)
    with (data_dir / "formal_jacobi_coefficients.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "a_n", "b_n", "h_n"])
        for n in range(max_degree):
            b_n = None if n == 0 else jacobi.subdiagonal[n]
            writer.writerow([
                n,
                fraction_string(jacobi.diagonal[n]),
                fraction_string(b_n),
                fraction_string(jacobi.norms[n]),
            ])

    exact_lines = ["Exact formal Jacobi/orthogonal-polynomial checks", ""]
    alternating_ok = all(
        jacobi.diagonal[n] == Fraction(-1 if n % 2 == 0 else 1)
        for n in range(max_degree)
    )
    recursive_ok = all(
        jacobi.subdiagonal[n] == recursive_b[n] for n in range(1, max_degree)
    )
    exact_lines.append(f"a_n=(-1)^(n+1) through n={max_degree-1}: {alternating_ok}")
    exact_lines.append(f"nonlinear dyadic b_n recursion through n={max_degree-1}: {recursive_ok}")
    exact_lines.append("")
    exact_lines.append("Dyadic polynomial identities p_(2^m)(x)=x^(2^m)+1:")
    for m in range(0, 7):
        N = 1 << m
        expected = [Fraction(0)] * (N + 1)
        expected[0] = expected[N] = Fraction(1)
        ok = jacobi.polynomials[N] == expected
        exact_lines.append(f"m={m}, N={N:2d}: {ok}; h_N={fraction_string(jacobi.norms[N])}")
    write_text(data_dir / "formal_jacobi_checks.txt", exact_lines)

    # Pade and quadrature checks.
    pade_lines = ["Dyadic Pade and antiperiodic quadrature checks", ""]
    z0 = mp.mpf("0.63")
    exact_E = signed_tm_ogf(z0)
    pade_errors: list[tuple[int, mp.mpf]] = []
    for m in range(0, 8):
        N = 1 << m
        approx = dyadic_pade(m, z0)
        err = abs(exact_E - approx)
        pade_errors.append((N, err))
        normalized = err / abs(z0) ** (2 * N)
        pade_lines.append(
            f"m={m:2d}, N={N:3d}, error={mp.nstr(err,12):>16}, "
            f"error/|z|^(2N)={mp.nstr(normalized,12)}"
        )
    pade_lines.append("")
    for m in range(1, 7):
        N = 1 << m
        max_residual = mp.mpf(0)
        for r in range(2 * N):
            residual = abs(antiperiodic_quadrature(m, r) - thue_morse_sign(r))
            max_residual = max(max_residual, residual)
        pade_lines.append(
            f"quadrature m={m}, N={N:2d}, max residual for 0<=r<2N: "
            f"{mp.nstr(max_residual,8)}"
        )
    write_text(data_dir / "pade_quadrature_checks.txt", pade_lines)

    # Exact moments and Mellin checks.
    moments = exact_up_moments(160)
    with (data_dir / "up_even_moments.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["order", "moment_exact", "moment_decimal"])
        for n in range(0, 41, 2):
            q = moments[n]
            writer.writerow([n, fraction_string(q), mp.nstr(mp.mpf(q.numerator) / q.denominator, 35)])

    mellin_lines = ["Mellin-moment checks", ""]
    for s in [mp.mpf("0.5"), mp.mpf("1.25"), mp.mpf("2.75"), mp.mpc("1.4", "0.3")]:
        series_value = mellin_y_series(s, moments)
        # The direct quadrature uses the sparse cosine-density representation.
        spline_value = mellin_y_from_cosine(s, coeffs)
        mellin_lines.append(
            f"s={mp.nstr(s,12):>14}  series={mp.nstr(series_value,18):>24}  "
            f"quadrature={mp.nstr(spline_value,18):>24}  diff={mp.nstr(abs(series_value-spline_value),8)}"
        )
    write_text(data_dir / "mellin_checks.txt", mellin_lines)

    # Malmsten checks.
    malmsten_lines = ["Bose--Malmsten integral checks for log Phi", ""]
    for z in [mp.mpf("0.2"), mp.mpf("0.6"), mp.mpc("0.35", "0.2")]:
        direct = mp.log(phi(z))
        integral = log_phi_malmsten(z)
        malmsten_lines.append(
            f"z={mp.nstr(z,12):>14}  direct={mp.nstr(direct,18):>24}  "
            f"integral={mp.nstr(integral,18):>24}  diff={mp.nstr(abs(direct-integral),8)}"
        )
    write_text(data_dir / "malmsten_checks.txt", malmsten_lines)

    # Figures are deliberately simple, one chart per figure, with default
    # Matplotlib colors/styles for portability.
    import matplotlib.pyplot as plt

    x = list(range(len(coeffs)))
    y = [float(-mp.log(abs(c))) for c in coeffs]
    fig = plt.figure(figsize=(7.2, 4.4))
    ax = fig.add_subplot(111)
    ax.plot(x, y, marker=".", linewidth=1)
    ax.set_xlabel(r"$k$")
    ax.set_ylabel(r"$-\log|\Phi(k+1/2)|$")
    ax.set_title("Decay of the half-lattice Fourier samples")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(fig_dir / "half_lattice_decay.pdf")
    fig.savefig(fig_dir / "half_lattice_decay.png", dpi=180)
    plt.close(fig)

    fig = plt.figure(figsize=(7.2, 4.4))
    ax = fig.add_subplot(111)
    truncations = [4, 8, 12, 16, 24, 32, 48, 64, 96, 128]
    for r in range(0, 5):
        errors = []
        for K in truncations:
            value = mp.fsum(coeffs[k] * (2 * k + 1) ** (2 * r) for k in range(K))
            target = mp.mpf("0.5") if r == 0 else mp.mpf(0)
            errors.append(max(float(abs(value - target)), 1e-300))
        ax.semilogy(truncations, errors, marker="o", label=fr"$r={r}$")
    ax.set_xlabel("number of half-lattice coefficients")
    ax.set_ylabel("absolute cancellation residual")
    ax.set_title("Weighted Thue--Morse cancellations from flatness")
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(fig_dir / "weighted_cancellations.pdf")
    fig.savefig(fig_dir / "weighted_cancellations.png", dpi=180)
    plt.close(fig)

    b_values = [float(jacobi.subdiagonal[n]) for n in range(1, 65)]
    fig = plt.figure(figsize=(7.2, 4.4))
    ax = fig.add_subplot(111)
    ax.plot(range(1, 65), b_values, marker=".", linewidth=0.9)
    ax.set_yscale("symlog", linthresh=1)
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"formal Jacobi coefficient $b_n$")
    ax.set_title("Nonlinear dyadic Jacobi coefficients for Thue--Morse")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(fig_dir / "formal_jacobi_coefficients.pdf")
    fig.savefig(fig_dir / "formal_jacobi_coefficients.png", dpi=180)
    plt.close(fig)

    fig = plt.figure(figsize=(7.2, 4.4))
    ax = fig.add_subplot(111)
    ax.semilogy([n for n, _ in pade_errors], [float(e) for _, e in pade_errors], marker="o")
    ax.set_xlabel(r"dyadic denominator degree $N=2^m$")
    ax.set_ylabel(r"$|E(0.63)-P_m(0.63)/(1+0.63^N)|$")
    ax.set_title("Double-order dyadic Padé convergence")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(fig_dir / "dyadic_pade_error.pdf")
    fig.savefig(fig_dir / "dyadic_pade_error.png", dpi=180)
    plt.close(fig)

    write_text(
        output_dir / "RUN_SUMMARY.txt",
        [
            "All experiment families completed successfully.",
            f"mpmath precision: {mp.mp.dps} decimal digits",
            f"half-lattice coefficients: {len(coeffs)}",
            f"formal Jacobi coefficients: {max_degree}",
            "See data/*.txt and data/*.csv for residuals and exact values.",
        ],
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("generated"),
        help="directory for generated data and figures (default: generated)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    generate_all(args.output_dir)
    print(f"Generated reproducibility package in {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
