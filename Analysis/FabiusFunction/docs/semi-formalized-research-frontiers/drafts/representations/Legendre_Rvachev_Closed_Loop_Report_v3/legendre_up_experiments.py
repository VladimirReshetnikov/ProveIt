#!/usr/bin/env python3
"""Exact and numerical experiments for the Legendre--Rvachev closed loop.

This script accompanies the report

    Legendre Polynomials in the Rvachev Up Dictionary:
    Symmetric Finite Synthesis, Closed Fourier--Legendre Loops,
    and Transmuted Spectral Geometry.

The calculations are deliberately split into two layers.

1. Exact symbolic layer (Python integers and SymPy rationals)
   * reciprocal moment-generating-function coefficients gamma_n;
   * deconvolved Legendre polynomials Q_n = M_u(D)^{-1} P_n;
   * the endpoint-coordinate matrix of central reflected atom pairs;
   * the exact q-product determinant certificate;
   * central-pair coefficients for P_{2m} at common scale 4^N;
   * exact Fourier--Legendre coefficients of the Rvachev up-function;
   * an exact Favard-recurrence obstruction for the Q_n family.

2. Floating-point diagnostic layer (NumPy)
   * evaluation of up from its half-integer cosine series;
   * low-degree checks of central-pair reconstructions;
   * measurement of cancellation and roundoff;
   * comparison of Legendre partial sums with the up-function;
   * high-precision root loci for Q_n through degree 20.

The exact identities do not depend on the numerical Fourier truncation.  The
floating-point calculations are included only to visualize stability,
cancellation, and spectral behavior.  All files are written next to this
script.  The code is intentionally explicit rather than optimized so that the
algebra can be audited line by line.
"""

from __future__ import annotations

import csv
import math
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import sympy as sp


HERE = Path(__file__).resolve().parent
X = sp.symbols("x")


# ---------------------------------------------------------------------------
# Exact polynomial and recurrence utilities
# ---------------------------------------------------------------------------


def multiply_integer_polynomials(a: Sequence[int], b: Sequence[int]) -> List[int]:
    """Return the coefficient list of the product of integer polynomials."""
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


@lru_cache(maxsize=None)
def annihilator_coefficients(d: int) -> Tuple[int, ...]:
    r"""Return coefficients of A_d(z)=prod_{m=1}^d [2^m]_z.

    Here [q]_z=1+z+...+z^{q-1}.  The degree is

        R_d = 2^(d+1)-d-2.

    The full polynomial grows exponentially, so this routine is used only for
    moderate direct checks.  The longer sigma table is computed by a separate
    truncated binary-partition algorithm.
    """
    if d < 0:
        raise ValueError("d must be nonnegative")
    a = [1]
    for m in range(1, d + 1):
        a = multiply_integer_polynomials(a, [1] * (2**m))
    return tuple(a)


def endpoint_coordinates_from_active_vector(
    d: int, q: Dict[int, sp.Expr | int]
) -> sp.Matrix:
    r"""Reduce active atom coefficients to the right endpoint basis.

    The normalized one-cell atoms are

        psi_k(t)=2^{-d} up((t-k)/2^d),  0<=t<=1,

    with active centers -M+1,...,M, M=2^d.  The annihilator theorem says that
    null coefficient sequences satisfy A_d(E)n=0.  We copy the first R_d
    entries of q into such a null sequence, extend it by the monic recurrence,
    and subtract.  The remainder is supported on the final d+2 centers and is
    the unique endpoint-coordinate vector.
    """
    if d < 0:
        raise ValueError("d must be nonnegative")
    M = 2**d
    a = annihilator_coefficients(d)
    R = len(a) - 1
    first = -M + 1

    # Initial recurrence data: the first R active coefficients.
    n: Dict[int, sp.Expr | int] = {
        k: q.get(k, 0) for k in range(first, first + R)
    }

    # A_d is monic and palindromic, so the forward recurrence can be written
    # with the coefficient order below.
    for j in range(first + R, M + 1):
        n[j] = -sum(a[r] * n[j - R + r] for r in range(R))

    endpoint_start = M - d - 1
    return sp.Matrix(
        [sp.simplify(q.get(k, 0) - n[k]) for k in range(endpoint_start, M + 1)]
    )


@lru_cache(maxsize=None)
def central_pair_endpoint_matrix(N: int) -> sp.ImmutableMatrix:
    r"""Return endpoint coordinates of the N+1 central reflected pairs.

    We use d=2N and M=4^N.  Column r is the coordinate vector of

        S_r(t)=psi_{-r}(t)+psi_{r+1}(t),  r=0,...,N.

    The full matrix has 2N+2 rows.  Its first N+1 rows form the square minor
    B_N used by the determinant theorem.
    """
    if N < 0:
        raise ValueError("N must be nonnegative")
    d = 2 * N
    columns = [
        endpoint_coordinates_from_active_vector(d, {-r: 1, r + 1: 1})
        for r in range(N + 1)
    ]
    return sp.ImmutableMatrix(sp.Matrix.hstack(*columns))


# ---------------------------------------------------------------------------
# Bernoulli--Bell / moment-generating-function calculus
# ---------------------------------------------------------------------------


def cumulants(max_degree: int) -> List[sp.Rational]:
    r"""Return cumulants kappa_n of the up probability law.

    kappa_{2r}=B_{2r}/(2r(1-4^{-r})); odd cumulants vanish.
    """
    kap = [sp.Rational(0)] * (max_degree + 1)
    for n in range(2, max_degree + 1, 2):
        r = n // 2
        kap[n] = sp.bernoulli(n) / (sp.Rational(n) * (1 - sp.Rational(1, 4) ** r))
    return kap


@lru_cache(maxsize=None)
def moments_and_reciprocal_coefficients(
    max_degree: int,
) -> Tuple[Tuple[sp.Rational, ...], Tuple[sp.Rational, ...]]:
    r"""Return moments mu_n and reciprocal-MGF coefficients gamma_n.

    M_u(z)=sum mu_n z^n/n!, and 1/M_u(z)=sum gamma_n z^n/n!.
    Both sequences are generated from cumulants by exact binomial recurrences.
    """
    kap = cumulants(max_degree)
    mu = [sp.Rational(0)] * (max_degree + 1)
    gam = [sp.Rational(0)] * (max_degree + 1)
    mu[0] = gam[0] = sp.Rational(1)
    for n in range(1, max_degree + 1):
        mu[n] = sp.simplify(
            sum(
                sp.binomial(n - 1, r - 1) * kap[r] * mu[n - r]
                for r in range(1, n + 1)
            )
        )
        gam[n] = sp.simplify(
            -sum(
                sp.binomial(n - 1, r - 1) * kap[r] * gam[n - r]
                for r in range(1, n + 1)
            )
        )
    return tuple(mu), tuple(gam)


def apply_reciprocal_mgf(poly: sp.Expr, scale: int = 1) -> sp.Expr:
    r"""Apply M_u(scale*D)^{-1} to a polynomial exactly."""
    degree = sp.Poly(poly, X).degree()
    _, gam = moments_and_reciprocal_coefficients(degree)
    return sp.expand(
        sum(
            gam[j] * scale**j * sp.diff(poly, X, j) / sp.factorial(j)
            for j in range(degree + 1)
        )
    )


def deconvolved_legendre(n: int) -> sp.Expr:
    """Return Q_n(x)=M_u(D)^{-1}P_n(x)."""
    return apply_reciprocal_mgf(sp.legendre(n, X))


def endpoint_coordinates_of_polynomial(poly: sp.Expr, d: int) -> sp.Matrix:
    r"""Return endpoint coordinates of a polynomial in the degree-d dictionary."""
    M = 2**d
    q_poly = sp.Poly(apply_reciprocal_mgf(poly, scale=M), X)
    active = {k: q_poly.eval(k) for k in range(-M + 1, M + 1)}
    return endpoint_coordinates_from_active_vector(d, active)


def central_legendre_coefficients(N: int, m: int) -> sp.Matrix:
    r"""Exact coefficients of P_{2m}(2t-1) in the N+1 central pair basis."""
    if not (0 <= m <= N):
        raise ValueError("require 0 <= m <= N")
    d = 2 * N
    full = central_pair_endpoint_matrix(N)
    square = full[: N + 1, :]
    target = endpoint_coordinates_of_polynomial(sp.legendre(2 * m, 2 * X - 1), d)
    c = square.inv() * target[: N + 1, :]
    if full * c != target:
        raise AssertionError("central coefficients failed the exact endpoint check")
    return sp.simplify(c)


# ---------------------------------------------------------------------------
# q-product / binary-partition determinant coefficients
# ---------------------------------------------------------------------------


def binary_partition_coefficients(max_N: int) -> List[int]:
    r"""Coefficients of prod_{m>=1}(1-z^{2^m})^{-1} through z^max_N."""
    p = [0] * (max_N + 1)
    p[0] = 1
    part = 2
    while part <= max_N:
        for k in range(part, max_N + 1):
            p[k] += p[k - part]
        part *= 2
    return p


def sigma_table(max_N: int) -> List[int]:
    r"""Compute sigma_N exactly for every 0<=N<=max_N.

        sigma_N=[z^N](1-z)^(2N-2)/prod_{m>=1}(1-z^{2^m}).

    Only parts at most N matter.  Precomputing their partition coefficients
    makes the complete table O(max_N^2), fast enough for exact checks through
    N=128.
    """
    if max_N < 0:
        raise ValueError("max_N must be nonnegative")
    p = binary_partition_coefficients(max_N)
    out = [0] * (max_N + 1)
    out[0] = 1
    for N in range(1, max_N + 1):
        out[N] = sum(
            (-1) ** j * math.comb(2 * N - 2, j) * p[N - j]
            for j in range(N + 1)
        )
    return out


@lru_cache(maxsize=None)
def sigma_binary_partition(N: int) -> int:
    """Compute a single sigma_N exactly."""
    return sigma_table(N)[N]


def determinant_formula(N: int, sigma: int | None = None) -> int:
    """Exact determinant of the central-pair endpoint minor B_N."""
    if N == 0:
        return 1
    if sigma is None:
        sigma = sigma_binary_partition(N)
    C_N = 2 ** (1 + N * (2 * N - 1))
    return (-1) ** N * (C_N * sigma - 1)


# ---------------------------------------------------------------------------
# Exact Fourier--Legendre coefficients of up
# ---------------------------------------------------------------------------


def expectation_of_polynomial(poly: sp.Expr, moments: Sequence[sp.Rational]) -> sp.Expr:
    """Evaluate E[p(Z)] from an exact moment table."""
    P = sp.Poly(sp.expand(poly), X)
    return sp.simplify(sum(coeff * moments[pow_[0]] for pow_, coeff in P.terms()))


def up_legendre_coefficients(max_N: int) -> List[sp.Rational]:
    r"""Return u_n=(4n+1)E[P_{2n}(Z)]/2 for n=0,...,max_N."""
    mu, _ = moments_and_reciprocal_coefficients(2 * max_N)
    out: List[sp.Rational] = []
    for n in range(max_N + 1):
        mean = expectation_of_polynomial(sp.legendre(2 * n, X), mu)
        out.append(sp.simplify(sp.Rational(4 * n + 1, 2) * mean))
    return out


# ---------------------------------------------------------------------------
# Numerical evaluation of up from the half-integer cosine series
# ---------------------------------------------------------------------------


def up_cosine_coefficients(term_count: int = 900, product_factors: int = 64) -> np.ndarray:
    r"""Return values of u-hat((2k+1)/2) for k=0,...,term_count-1."""
    k = np.arange(term_count, dtype=float)
    xi = (2.0 * k + 1.0) / 2.0
    coeff = np.ones(term_count, dtype=float)
    for j in range(product_factors):
        coeff *= np.sinc(xi / (2.0**j))
    return coeff


def up_values(points: np.ndarray, cosine_coeff: np.ndarray) -> np.ndarray:
    r"""Evaluate up by u(x)=1/2+sum_k u-hat((2k+1)/2)cos((2k+1)pi x)."""
    points = np.asarray(points, dtype=float)
    flat = points.ravel()
    result = np.zeros_like(flat)
    mask = np.abs(flat) <= 1.0 + 2e-15
    inside = np.clip(flat[mask], -1.0, 1.0)
    odd = 2.0 * np.arange(len(cosine_coeff), dtype=float) + 1.0

    values = np.empty_like(inside)
    batch = 256
    for start in range(0, len(inside), batch):
        stop = min(start + batch, len(inside))
        phase = np.pi * inside[start:stop, None] * odd[None, :]
        values[start:stop] = 0.5 + np.cos(phase) @ cosine_coeff
    result[mask] = values
    return result.reshape(points.shape)


def evaluate_central_atomization(
    xgrid: np.ndarray,
    N: int,
    coefficients: Sequence[sp.Expr],
    cosine_coeff: np.ndarray,
) -> np.ndarray:
    r"""Evaluate a central-pair synthesis in ordinary double precision."""
    M = float(4**N)
    out = np.zeros_like(xgrid, dtype=float)
    for r, exact_c in enumerate(coefficients):
        a = float(2 * r + 1)
        raw = float(sp.N(exact_c, 30)) / M
        out += raw * (
            up_values((xgrid - a) / (2.0 * M), cosine_coeff)
            + up_values((xgrid + a) / (2.0 * M), cosine_coeff)
        )
    return out


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    """Write a UTF-8 CSV file."""
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def monic(poly: sp.Expr) -> sp.Expr:
    """Return the monic normalization of a nonzero polynomial."""
    return sp.Poly(poly, X).monic().as_expr()


def main() -> None:
    # 1. Reciprocal-MGF and deconvolved Legendre data.
    mu, gam = moments_and_reciprocal_coefficients(40)
    q_polys = [deconvolved_legendre(n) for n in range(21)]

    # 2. Direct recurrence verification of the central determinant theorem.
    direct_rows = []
    for N in range(0, 6):
        full = central_pair_endpoint_matrix(N)
        minor = full[: N + 1, :]
        direct_det = int(minor.det())
        predicted = determinant_formula(N)
        direct_rows.append((N, 4**N, full.rank(), direct_det, predicted, direct_det == predicted))
        if direct_det != predicted or full.rank() != N + 1:
            raise AssertionError(f"central determinant check failed at N={N}")
    write_csv(
        HERE / "direct_determinant_checks.csv",
        ["N", "M=4^N", "rank", "direct_det", "formula_det", "match"],
        direct_rows,
    )

    # 3. Exact sigma table through N=128.  The short table includes complete
    #    determinants; the long table omits them to avoid megabyte-size integers.
    sigmas = sigma_table(128)
    sigma_rows = []
    for N in range(0, 65):
        sigma = sigmas[N]
        det = determinant_formula(N, sigma)
        C = 1 if N == 0 else 2 ** (1 + N * (2 * N - 1))
        baseline = ""
        ratio = ""
        if N >= 2:
            baseline_int = (-1) ** N * 2 ** (2 * N - 3)
            baseline = baseline_int
            ratio = sigma / baseline_int
        sigma_rows.append((N, sigma, C, det, det.bit_length(), baseline, ratio))
    write_csv(
        HERE / "sigma_binary_partition.csv",
        [
            "N",
            "sigma_N",
            "C_N",
            "det_B_N",
            "det_bit_length",
            "simple_baseline",
            "sigma_over_baseline",
        ],
        sigma_rows,
    )
    write_csv(
        HERE / "sigma_sign_checks_0_128.csv",
        ["N", "sigma_N", "alternating_sign_holds"],
        [
            (N, sigmas[N], (N < 2) or (((-1) ** N) * sigmas[N] > 0))
            for N in range(129)
        ],
    )

    # 4. Exact central-pair coefficients.  N=4 already exposes the conditioning
    #    trend while keeping the CSV readable.
    central_rows = []
    central_cache: Dict[Tuple[int, int], sp.Matrix] = {}
    for N in range(0, 5):
        for m in range(0, N + 1):
            c = central_legendre_coefficients(N, m)
            central_cache[(N, m)] = c
            M = 4**N
            for r, cr in enumerate(c):
                central_rows.append(
                    (
                        N,
                        m,
                        r,
                        str(sp.factor(cr)),
                        str(sp.factor(cr / M)),
                        float(abs(sp.N(cr / M, 20))),
                    )
                )
    write_csv(
        HERE / "central_legendre_coefficients.csv",
        [
            "common_N",
            "legendre_m",
            "pair_r",
            "normalized_c",
            "raw_amplitude_c_over_M",
            "abs_raw_float",
        ],
        central_rows,
    )

    # 5. Exact up-Legendre coefficients and common-scale closed-loop amplitudes.
    u_coeff = up_legendre_coefficients(12)
    write_csv(
        HERE / "up_legendre_coefficients.csv",
        ["n", "u_n_exact", "u_n_decimal"],
        [(n, str(v), f"{float(sp.N(v, 18)):.17g}") for n, v in enumerate(u_coeff)],
    )

    closed_rows = []
    closed_cache: Dict[int, sp.Matrix] = {}
    for N in range(0, 5):
        alpha = sp.zeros(N + 1, 1)
        for m in range(N + 1):
            alpha += u_coeff[m] * central_cache[(N, m)]
        closed_cache[N] = sp.simplify(alpha)
        M = 4**N
        for r, ar in enumerate(alpha):
            closed_rows.append(
                (N, r, str(sp.factor(ar)), str(sp.factor(ar / M)), float(abs(sp.N(ar / M, 20))))
            )
    write_csv(
        HERE / "closed_loop_central_coefficients.csv",
        ["N", "pair_r", "alpha_Nr", "raw_amplitude_alpha_over_M", "abs_raw_float"],
        closed_rows,
    )

    # 6. Exact Favard obstruction.  If the monic Q_n formed a scalar orthogonal
    #    polynomial sequence, parity would force a three-term recurrence.  At
    #    degree four an unavoidable Q_0 term appears.
    qmonic = [monic(q) for q in q_polys]
    favard_residual = sp.expand(
        qmonic[4] - (X * qmonic[3] - sp.Rational(62, 105) * qmonic[2])
    )
    if favard_residual != -sp.Rational(8, 225):
        raise AssertionError("unexpected Favard residual")
    (HERE / "favard_obstruction.txt").write_text(
        "Monic deconvolved Legendre polynomials satisfy\n"
        "  q_4 = x q_3 - (62/105) q_2 - (8/225) q_0.\n"
        "The nonzero q_0 term violates the scalar Favard three-term form.\n",
        encoding="utf-8",
    )

    # 7. Root locus and exact Sturm counts.  The root locations are numerical,
    #    but the number of real roots is certified in exact rational arithmetic.
    sturm_rows = []
    exact_nonreal_counts: Dict[int, int] = {}
    for n in range(1, 21):
        qpoly = sp.Poly(q_polys[n], X, domain=sp.QQ)
        real_count = int(qpoly.count_roots(-sp.oo, sp.oo))
        exact_nonreal_counts[n] = n - real_count
        sturm_rows.append((n, real_count, n - real_count))
    write_csv(
        HERE / "sturm_real_root_counts.csv",
        ["n", "exact_real_root_count", "exact_nonreal_root_count"],
        sturm_rows,
    )

    # A compact, independently checkable Sturm certificate for Q_12 records
    # degrees and leading signs of the exact rational Sturm chain.  Signs at
    # +/- infinity give 10 and 2 variations, hence 8 real roots.
    q12_sturm = sp.sturm(q_polys[12], X)
    degree_signs = []
    plus_signs = []
    minus_signs = []
    for poly in q12_sturm:
        P = sp.Poly(poly, X, domain=sp.QQ)
        lead_sign = int(sp.sign(P.LC()))
        degree_signs.append((P.degree(), lead_sign))
        plus_signs.append(lead_sign)
        minus_signs.append(lead_sign if P.degree() % 2 == 0 else -lead_sign)
    variations = lambda signs: sum(a * b < 0 for a, b in zip(signs, signs[1:]))
    (HERE / "Q12_sturm_certificate.txt").write_text(
        "Exact rational Sturm certificate for Q_12\n"
        + "degree, leading-sign pairs: " + repr(degree_signs) + "\n"
        + "signs at -infinity: " + repr(minus_signs)
        + f"; variations={variations(minus_signs)}\n"
        + "signs at +infinity: " + repr(plus_signs)
        + f"; variations={variations(plus_signs)}\n"
        + "real roots = 10-2 = 8; nonreal roots = 12-8 = 4.\n",
        encoding="utf-8",
    )

    root_rows = []
    root_points = []
    nonreal_counts: Dict[int, int] = {}
    for n in range(1, 21):
        roots = sp.nroots(q_polys[n], n=50, maxsteps=1000)
        nonreal_count = 0
        for j, z in enumerate(roots):
            re = float(sp.re(z))
            im = float(sp.im(z))
            is_nonreal = abs(im) > 1e-12
            nonreal_count += int(is_nonreal)
            root_rows.append((n, j, f"{re:.17g}", f"{im:.17g}", is_nonreal))
            root_points.append((re, im, n))
        if nonreal_count % 4 != 0:
            raise AssertionError(f"unexpected nonreal-root count at n={n}")
        if nonreal_count != exact_nonreal_counts[n]:
            raise AssertionError(f"numerical and exact root counts disagree at n={n}")
        nonreal_counts[n] = nonreal_count
    write_csv(
        HERE / "deconvolved_legendre_roots.csv",
        ["n", "root_index", "real_part", "imag_part", "nonreal"],
        root_rows,
    )

    plt.figure(figsize=(8.0, 5.5))
    plt.scatter(
        np.array([p[0] for p in root_points]),
        np.array([p[1] for p in root_points]),
        s=15,
        alpha=0.75,
    )
    plt.axhline(0.0, linewidth=0.8)
    plt.xlabel(r"$\Re z$")
    plt.ylabel(r"$\Im z$")
    plt.title(r"Root locus of $Q_n=M_u(D)^{-1}P_n$, $1\leq n\leq20$")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(HERE / "deconvolved_legendre_root_locus.png", dpi=200)
    plt.close()

    # 8. Floating-point diagnostics.
    cosine_coeff = up_cosine_coefficients(term_count=900, product_factors=64)
    xgrid = np.linspace(-1.0, 1.0, 801)
    ugrid = up_values(xgrid, cosine_coeff)

    roundoff_rows = []
    p_errors: Dict[int, np.ndarray] = {}
    loop_errors: Dict[int, np.ndarray] = {}
    for N in range(1, 5):
        c = central_cache[(N, N)]
        atom_p = evaluate_central_atomization(xgrid, N, c, cosine_coeff)
        basis = np.zeros(2 * N + 1)
        basis[2 * N] = 1.0
        exact_p = np.polynomial.legendre.legval(xgrid, basis)
        p_error = np.abs(atom_p - exact_p)
        p_errors[N] = p_error

        atom_loop = evaluate_central_atomization(xgrid, N, closed_cache[N], cosine_coeff)
        poly_loop = np.zeros_like(xgrid)
        for m in range(N + 1):
            basis = np.zeros(2 * m + 1)
            basis[2 * m] = 1.0
            poly_loop += float(u_coeff[m]) * np.polynomial.legendre.legval(xgrid, basis)
        loop_error = np.abs(atom_loop - poly_loop)
        loop_errors[N] = loop_error

        roundoff_rows.append(
            (
                N,
                max(float(abs(sp.N(v / (4**N), 20))) for v in c),
                float(np.max(p_error)),
                max(float(abs(sp.N(v / (4**N), 20))) for v in closed_cache[N]),
                float(np.max(loop_error)),
                float(np.max(np.abs(ugrid - poly_loop))),
            )
        )

    write_csv(
        HERE / "floating_point_diagnostics.csv",
        [
            "N",
            "max_abs_raw_P2N_coefficient",
            "max_error_P2N_atomization",
            "max_abs_raw_closed_loop_coefficient",
            "max_error_closed_loop_atomization_vs_polynomial",
            "max_Legendre_partial_sum_error_vs_up",
        ],
        roundoff_rows,
    )

    plt.figure(figsize=(8.0, 5.0))
    for N in range(1, 5):
        plt.semilogy(xgrid, np.maximum(p_errors[N], 1e-18), label=rf"$P_{{{2*N}}}$")
    plt.xlabel(r"$x$")
    plt.ylabel("absolute reconstruction error")
    plt.title("Roundoff in exact central-pair Legendre atomizations")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(HERE / "central_pair_roundoff.png", dpi=200)
    plt.close()

    plt.figure(figsize=(8.0, 5.0))
    for N in (1, 2, 4, 8, 12):
        partial = np.zeros_like(xgrid)
        for m in range(N + 1):
            basis = np.zeros(2 * m + 1)
            basis[2 * m] = 1.0
            partial += float(u_coeff[m]) * np.polynomial.legendre.legval(xgrid, basis)
        plt.semilogy(
            xgrid,
            np.maximum(np.abs(ugrid - partial), 1e-18),
            label=rf"$N={N}$",
        )
    plt.xlabel(r"$x$")
    plt.ylabel(r"$|u(x)-S_N(x)|$")
    plt.title("Fourier--Legendre partial-sum error for the up-function")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(HERE / "legendre_partial_sum_error.png", dpi=200)
    plt.close()

    Ns = np.arange(2, 65)
    ratios = np.array(
        [sigmas[int(N)] / ((-1) ** int(N) * 2 ** (2 * int(N) - 3)) for N in Ns],
        dtype=float,
    )
    plt.figure(figsize=(8.0, 5.0))
    plt.plot(Ns, ratios, marker="o", markersize=2.5)
    plt.axvline(8, linestyle="--", linewidth=1.0)
    plt.xlabel(r"$N$")
    plt.ylabel(r"$\sigma_N/[(-1)^N2^{2N-3}]$")
    plt.title("Binary-partition correction in the central-pair determinant")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(HERE / "sigma_binary_partition_ratio.png", dpi=200)
    plt.close()

    # 9. Human-readable audit summary.
    all_signs = all((N < 2) or (((-1) ** N) * sigmas[N] > 0) for N in range(129))
    with (HERE / "numerical_results.txt").open("w", encoding="utf-8") as f:
        f.write("LEGENDRE--RVACHEV EXACT/NUMERICAL EXPERIMENTS\n")
        f.write("================================================\n\n")
        f.write("Reciprocal-MGF coefficients gamma_{2r}:\n")
        for n in range(0, 17, 2):
            f.write(f"  gamma_{n} = {gam[n]}\n")
        f.write("\nDeconvolved Legendre polynomials Q_n=M_u(D)^{-1}P_n:\n")
        for n, q in enumerate(q_polys[:9]):
            f.write(f"  Q_{n}(x) = {sp.factor(q)}\n")
        f.write("\nDirect central determinant checks:\n")
        for row in direct_rows:
            f.write(
                f"  N={row[0]} M={row[1]} rank={row[2]} "
                f"det={row[3]} formula={row[4]} match={row[5]}\n"
            )
        f.write("\nFirst sigma_N values:\n")
        for N in range(0, 17):
            f.write(f"  sigma_{N} = {sigmas[N]}\n")
        f.write(
            f"\nAlternating-sign conjecture verified exactly for all 2<=N<=128: {all_signs}.\n"
        )
        f.write("\nExact up-Legendre coefficients:\n")
        for n, value in enumerate(u_coeff):
            f.write(f"  u_{n} = {value}\n")
        f.write("\nExact Favard obstruction:\n")
        f.write("  q_4 = x q_3 - (62/105)q_2 - (8/225)q_0.\n")
        f.write("\nExact Sturm root count:\n")
        f.write("  Q_n has exactly n real roots for 1 <= n <= 11.\n")
        f.write("  Q_12 has exactly 8 real and 4 nonreal roots.\n")
        f.write("\nNumerical root locations:\n")
        f.write("  The first nonreal quartet occurs at n=12, near\n")
        f.write("  +/-1.58181382985647 +/- 0.189564695738147 i.\n")
        f.write("  Nonreal-root counts for n=12,...,20: ")
        f.write(", ".join(str(nonreal_counts[n]) for n in range(12, 21)) + "\n")
        f.write("\nFloating-point diagnostics:\n")
        for row in roundoff_rows:
            f.write(
                f"  N={row[0]} max|raw P coefficient|={row[1]:.6e}, "
                f"P atom error={row[2]:.6e}, "
                f"max|raw loop coefficient|={row[3]:.6e}, "
                f"loop atom-vs-polynomial error={row[4]:.6e}, "
                f"partial-sum error={row[5]:.6e}\n"
            )
        f.write("\nInterpretation:\n")
        f.write(
            "  Endpoint-coordinate and determinant checks are exact.  The\n"
            "  nonzero floating residuals come from evaluating huge signed atom\n"
            "  coefficients in IEEE double precision.  They are not defects of\n"
            "  the functional identities.  Stable evaluation should preserve\n"
            "  Legendre blocks or use a Gram-metric-aware atom algorithm.\n"
        )

    print("Generated exact tables, diagnostics, and figures in", HERE)


if __name__ == "__main__":
    main()
