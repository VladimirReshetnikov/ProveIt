#!/usr/bin/env python3
"""Numerical and symbolic experiments for the Lagrange--Legendre--Rvachev loop.

This script supports the report
    Closing the Lagrange--Legendre--Rvachev Loop.

It verifies, independently of the LaTeX derivations, the following identities.

1. Literal-shift polynomial synthesis on [-1,1]:

       p(x) = (1/M) sum_{|k|<2M} (D_up p)(k/M) up(x-k/M),

   for deg(p) <= d and M=2^d, where D_up = M_up(D)^(-1).

2. For Lagrange cardinal polynomials, the atom coefficient matrix B is a
   right inverse of the up-shift collocation matrix U:

       U B = I.

   Consequently B U is an idempotent (generally oblique) projector.

3. At Gauss--Legendre nodes, B factors through the Legendre Vandermonde
   matrix and the deconvolved Legendre polynomials Q_n = D_up P_n:

       B = D V^{-1},
       V^{-1}_{n,j} = ((2n+1)/2) w_j P_n(xi_j).

4. The exact d+2-atom endpoint compression from the repository also gives a
   right inverse.  A high-precision cosine-series evaluation of up verifies
   this strongly cancellation-prone identity.

5. Legendre partial sums and Lagrange interpolants can be atomized exactly in
   exact arithmetic.  Floating-point experiments quantify the cancellation
   and conditioning introduced by deconvolution.

Dependencies: Python 3.11+, numpy, sympy, mpmath, matplotlib.
No network access is used.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp

# Matplotlib is imported lazily so --no-plots still works in minimal setups.

X = sp.symbols("x")
Z = sp.symbols("z")


def cumulants(max_n: int) -> list[sp.Rational]:
    """Return centered up-law cumulants kappa_0,...,kappa_max_n.

    Odd cumulants vanish and
        kappa_{2r} = B_{2r} / (2r (1-4^{-r})).
    """
    out: list[sp.Rational] = [sp.Rational(0) for _ in range(max_n + 1)]
    for r in range(1, max_n // 2 + 1):
        out[2 * r] = sp.simplify(
            sp.bernoulli(2 * r)
            / (sp.Integer(2 * r) * (1 - sp.Rational(1, 4) ** r))
        )
    return out


def exponential_coefficients(max_n: int, inverse: bool) -> list[sp.Expr]:
    """Coefficients of M(z) or 1/M(z) in exponential generating form.

    Returns c_n such that
        M(z)^{+1 or -1} = sum c_n z^n/n! + O(z^{max_n+1}).
    """
    kappas = cumulants(max_n)
    log_series = sum(
        kappas[n] * Z**n / sp.factorial(n)
        for n in range(1, max_n + 1)
        if kappas[n] != 0
    )
    if inverse:
        log_series = -log_series
    series = sp.series(sp.exp(log_series), Z, 0, max_n + 1).removeO().expand()
    return [sp.simplify(sp.factorial(n) * series.coeff(Z, n)) for n in range(max_n + 1)]


def moment_coefficients(max_n: int) -> list[sp.Expr]:
    """Moments mu_n of the centered up law."""
    return exponential_coefficients(max_n, inverse=False)


def reciprocal_coefficients(max_n: int) -> list[sp.Expr]:
    """Reciprocal-MGF coefficients gamma_n of 1/M(z)."""
    return exponential_coefficients(max_n, inverse=True)


def appell_polynomials(max_n: int) -> list[sp.Expr]:
    """Return A_n(x) defined by exp(xz)/M(z)=sum A_n(x) z^n/n!."""
    gamma = reciprocal_coefficients(max_n)
    result: list[sp.Expr] = []
    for n in range(max_n + 1):
        poly = sum(
            sp.binomial(n, r) * gamma[r] * X ** (n - r)
            for r in range(n + 1)
        )
        result.append(sp.expand(poly))
    return result


def deconvolve_polynomial(poly: sp.Expr, variable: sp.Symbol = X, rho: sp.Expr = 1) -> sp.Expr:
    """Apply M_up(rho D)^(-1) to a polynomial exactly."""
    degree = int(sp.degree(poly, variable))
    gamma = reciprocal_coefficients(degree)
    answer = sp.Integer(0)
    for r in range(degree + 1):
        if gamma[r] != 0:
            answer += (
                gamma[r]
                * rho**r
                * sp.diff(poly, variable, r)
                / sp.factorial(r)
            )
    return sp.expand(answer)


def deconvolved_legendre_polynomials(max_n: int) -> list[sp.Expr]:
    """Return Q_n = M_up(D)^(-1) P_n for n<=max_n."""
    return [deconvolve_polynomial(sp.legendre(n, X), X, 1) for n in range(max_n + 1)]


def exact_up_legendre_coefficients(max_index: int) -> list[sp.Expr]:
    """Return exact u_n in up(x)=sum_{n>=0} u_n P_{2n}(x).

    The expectation of P_{2n}(Y) is evaluated from exact centered moments.
    """
    moments = moment_coefficients(2 * max_index)
    output: list[sp.Expr] = []
    for n in range(max_index + 1):
        polynomial = sp.Poly(sp.legendre(2 * n, X), X)
        expectation = sp.Integer(0)
        for (power,), coefficient in polynomial.terms():
            expectation += coefficient * moments[power]
        output.append(sp.simplify(sp.Rational(4 * n + 1, 2) * expectation))
    return output


class UpFFT:
    """Fast evaluator for the Rvachev up-function using its Fourier product.

    The period L is chosen larger than the support width, so the inverse FFT
    recovers the non-overlapping periodization of up.  Linear interpolation on
    a fine grid is sufficient for the double-precision matrix experiments.
    """

    def __init__(self, grid_power: int = 19, period: float = 8.0, factors: int = 42):
        self.n = 1 << grid_power
        self.period = float(period)
        self.dx = self.period / self.n
        frequencies = np.fft.fftfreq(self.n, d=self.dx)
        transform = np.ones(self.n, dtype=np.float64)
        for j in range(factors):
            # numpy.sinc(y)=sin(pi*y)/(pi*y), exactly the repository convention.
            transform *= np.sinc(frequencies / (2.0**j))
        values = np.fft.ifft(transform).real / self.dx
        self.values = np.fft.fftshift(values)
        self.grid = (np.arange(self.n) - self.n // 2) * self.dx

    def __call__(self, points: np.ndarray | Sequence[float] | float) -> np.ndarray | float:
        arr = np.asarray(points, dtype=np.float64)
        flat = arr.ravel()
        result = np.zeros_like(flat)
        interior = np.abs(flat) < 1.0
        result[interior] = np.interp(flat[interior], self.grid, self.values)
        result = result.reshape(arr.shape)
        if np.isscalar(points):
            return float(result)
        return result

    def diagnostics(self) -> dict[str, float]:
        integral = float(np.sum(self.values) * self.dx)
        at_zero = float(np.interp(0.0, self.grid, self.values))
        minimum = float(np.min(self.values))
        return {"integral": integral, "up(0)": at_zero, "minimum_grid_value": minimum}


def polynomial_to_numpy(poly: sp.Expr) -> np.ndarray:
    """Convert a SymPy power-basis polynomial to descending float coefficients."""
    p = sp.Poly(sp.expand(poly), X)
    return np.array([float(c) for c in p.all_coeffs()], dtype=np.float64)


def evaluate_symbolic_polys(polys: Sequence[sp.Expr], points: np.ndarray) -> np.ndarray:
    """Evaluate polys at points; result has shape (len(points), len(polys))."""
    out = np.empty((len(points), len(polys)), dtype=np.float64)
    for j, poly in enumerate(polys):
        out[:, j] = np.polyval(polynomial_to_numpy(poly), points)
    return out


def lattice_indices(degree: int) -> tuple[int, np.ndarray]:
    """Return M=2^degree and the nontrivial shifts |k|<2M."""
    m = 1 << degree
    return m, np.arange(-2 * m + 1, 2 * m, dtype=np.int64)


def gauss_matrices(degree: int, up: UpFFT, q_polys: Sequence[sp.Expr]):
    """Construct U,V,D,B for degree-d Gauss--Legendre nodes."""
    nodes, weights = np.polynomial.legendre.leggauss(degree + 1)
    m, shifts = lattice_indices(degree)
    centers = shifts / m
    vander = np.polynomial.legendre.legvander(nodes, degree)
    q_values = evaluate_symbolic_polys(q_polys[: degree + 1], centers)
    d_matrix = q_values / m
    v_inv = np.linalg.inv(vander)
    b_matrix = d_matrix @ v_inv
    u_matrix = up(nodes[:, None] - centers[None, :])
    return nodes, weights, m, shifts, centers, u_matrix, vander, d_matrix, b_matrix


def spectral_norm(matrix: np.ndarray) -> float:
    """Largest singular value, efficient for tall skinny matrices."""
    return float(np.linalg.svd(matrix, compute_uv=False)[0])


def smallest_nonzero_singular_value(matrix: np.ndarray) -> float:
    values = np.linalg.svd(matrix, compute_uv=False)
    return float(values[-1])


def exact_lagrange_polynomials(nodes: Sequence[sp.Expr], variable: sp.Symbol) -> list[sp.Expr]:
    output: list[sp.Expr] = []
    for j, node in enumerate(nodes):
        poly = sp.Integer(1)
        for r, other in enumerate(nodes):
            if r != j:
                poly *= (variable - other) / (node - other)
        output.append(sp.expand(poly))
    return output


def annihilator_coefficients(degree: int) -> list[sp.Integer]:
    """Ascending coefficients of A_d(z)=prod_{m=1}^d [2^m]_z."""
    zz = sp.symbols("zz")
    polynomial = sp.Integer(1)
    for m in range(1, degree + 1):
        polynomial *= sum(zz**r for r in range(2**m))
    p = sp.Poly(sp.expand(polynomial), zz)
    return [sp.Integer(c) for c in reversed(p.all_coeffs())]


def endpoint_compressed_lagrange_matrix(
    degree: int, nodes_x: Sequence[sp.Expr]
) -> tuple[list[int], sp.Matrix]:
    """Exact d+2-atom endpoint coefficient matrix for Lagrange cardinals.

    This specializes the endpoint-basis compression in Up_Polynomial_Synthesis.
    The input nodes are on [-1,1].  Internally t=(x+1)/2 maps to [0,1].
    """
    if len(nodes_x) != degree + 1:
        raise ValueError("Need degree+1 interpolation nodes")
    t = sp.symbols("t")
    nodes_t = [(node + 1) / 2 for node in nodes_x]
    lagrange = exact_lagrange_polynomials(nodes_t, t)
    m = 1 << degree
    q_polys = [deconvolve_polynomial(poly, t, rho=m) for poly in lagrange]

    active = list(range(-m + 1, m + 1))
    recurrence_degree = 2 * m - degree - 2
    a = annihilator_coefficients(degree)
    assert len(a) == recurrence_degree + 1 and a[-1] == 1
    retained = active[recurrence_degree:]
    assert len(retained) == degree + 2

    b_matrix = sp.zeros(degree + 2, degree + 1)
    for j, q_poly in enumerate(q_polys):
        q_values = {k: sp.simplify(q_poly.subs(t, k)) for k in active}
        null_values: dict[int, sp.Expr] = {}
        for k in active[:recurrence_degree]:
            null_values[k] = q_values[k]
        for position in range(recurrence_degree, len(active)):
            k = active[position]
            base = k - recurrence_degree
            null_values[k] = -sum(
                a[r] * null_values[base + r] for r in range(recurrence_degree)
            )
        for r, k in enumerate(retained):
            b_matrix[r, j] = sp.simplify(q_values[k] - null_values[k])
    return retained, b_matrix


def half_integer_fourier_coefficients(count: int, dps: int = 80) -> list[mp.mpf]:
    """Return Phi((2r+1)/2), r=0,...,count-1, at high precision."""
    mp.mp.dps = dps
    coeffs: list[mp.mpf] = []
    two = mp.mpf(2)
    for r in range(count):
        xi = mp.mpf(2 * r + 1) / 2
        product = mp.mpf(1)
        # 120 factors are far beyond what 80-digit arithmetic needs here.
        for j in range(120):
            y = mp.pi * xi / (two**j)
            product *= mp.sin(y) / y
        coeffs.append(product)
    return coeffs


def high_precision_up(x: mp.mpf, coeffs: Sequence[mp.mpf]) -> mp.mpf:
    """Evaluate up on [-1,1] by the exact odd-half-integer cosine series."""
    x = mp.mpf(x)
    if abs(x) >= 1:
        return mp.mpf(0)
    total = mp.mpf("0.5")
    for r, coefficient in enumerate(coeffs):
        total += coefficient * mp.cos((2 * r + 1) * mp.pi * x)
    return total


def verify_endpoint_compression(output_dir: Path) -> dict[str, str]:
    """High-precision verification of the minimal d+2-atom right inverse."""
    degree = 4
    rational_nodes = [
        sp.Rational(-1),
        sp.Rational(-1, 2),
        sp.Rational(0),
        sp.Rational(1, 2),
        sp.Rational(1),
    ]
    retained, b_exact = endpoint_compressed_lagrange_matrix(degree, rational_nodes)
    m = 1 << degree
    nodes_t = [(node + 1) / 2 for node in rational_nodes]

    mp.mp.dps = 80
    coeffs = half_integer_fourier_coefficients(3000, dps=80)
    u_matrix = mp.matrix(degree + 1, degree + 2)
    for i, t_i in enumerate(nodes_t):
        t_mp = mp.mpf(str(sp.N(t_i, 90)))
        for r, k in enumerate(retained):
            u_matrix[i, r] = high_precision_up((t_mp - k) / m, coeffs) / m

    b_mp = mp.matrix(
        [
            [mp.mpf(str(sp.N(b_exact[r, j], 90))) for j in range(degree + 1)]
            for r in range(degree + 2)
        ]
    )
    product = u_matrix * b_mp
    max_error = max(
        abs(product[i, j] - (1 if i == j else 0))
        for i in range(degree + 1)
        for j in range(degree + 1)
    )

    text_path = output_dir / "endpoint_compression_certificate.txt"
    with text_path.open("w", encoding="utf-8") as handle:
        handle.write("Exact d+2-atom endpoint compression certificate\n")
        handle.write("degree d = 4, M = 16\n")
        handle.write(f"retained integer centers k = {retained}\n")
        handle.write("nodes on [-1,1] = -1, -1/2, 0, 1/2, 1\n\n")
        handle.write("Exact coefficient matrix B (rows are retained atoms):\n")
        handle.write(str(b_exact))
        handle.write("\n\nHigh-precision U B:\n")
        for i in range(degree + 1):
            handle.write("  " + "  ".join(mp.nstr(product[i, j], 35) for j in range(degree + 1)) + "\n")
        handle.write(f"\nmax |UB-I| = {mp.nstr(max_error, 40)}\n")
        handle.write(
            "The residual is dominated by truncating the cosine series after 3000 terms; "
            "the exact symbolic construction has UB=I.\n"
        )

    # Also emit the smaller d=2 matrix used as a readable worked example.
    retained2, b2 = endpoint_compressed_lagrange_matrix(
        2, [sp.Rational(-1), sp.Rational(0), sp.Rational(1)]
    )
    example_path = output_dir / "endpoint_degree2_matrix.tex"
    with example_path.open("w", encoding="utf-8") as handle:
        handle.write("% Generated by experiments.py\n")
        handle.write(
            "% LOCAL-NON-FOURIER-HAT: \\GeneratedEndpointCoefficientMatrix "
            "denotes the generated endpoint-basis coefficient matrix augmented "
            "by one endpoint atom\n"
        )
        handle.write(
            "\\newcommand{\\GeneratedEndpointCoefficientMatrix}{\\widehat B}\n"
        )
        handle.write("\\[\n")
        handle.write("\\GeneratedEndpointCoefficientMatrix_2=")
        handle.write(sp.latex(b2))
        handle.write(",\\qquad k=")
        handle.write(sp.latex(sp.Tuple(*retained2)))
        handle.write(".\n\\]\n")

    return {
        "degree": str(degree),
        "max_error": mp.nstr(max_error, 12),
        "max_coefficient": str(max(abs(value) for value in b_exact)),
    }


def reconstruct_from_atoms(
    evaluation_points: np.ndarray,
    centers: np.ndarray,
    coefficients: np.ndarray,
    up: UpFFT,
    chunk_size: int = 256,
) -> np.ndarray:
    """Evaluate sum_k coefficients[k] up(x-centers[k]) in chunks."""
    result = np.zeros_like(evaluation_points, dtype=np.float64)
    for start in range(0, len(evaluation_points), chunk_size):
        chunk = evaluation_points[start : start + chunk_size]
        values = up(chunk[:, None] - centers[None, :])
        result[start : start + chunk_size] = values @ coefficients
    return result


def run_matrix_checks(
    output_dir: Path, up: UpFFT, q_polys: Sequence[sp.Expr], degrees: Iterable[int]
) -> list[dict[str, float | int]]:
    rows: list[dict[str, float | int]] = []
    for degree in degrees:
        (
            nodes,
            weights,
            m,
            shifts,
            centers,
            u_matrix,
            vander,
            d_matrix,
            b_matrix,
        ) = gauss_matrices(degree, up, q_polys)
        identity_error = float(np.max(np.abs(u_matrix @ b_matrix - np.eye(degree + 1))))
        legendre_error = float(np.max(np.abs(u_matrix @ d_matrix - vander)))
        projector = b_matrix @ u_matrix
        projector_error = float(np.max(np.abs(projector @ projector - projector)))
        trace_error = float(abs(np.trace(projector) - (degree + 1)))
        row_sum_error = float(np.max(np.abs(b_matrix.sum(axis=1) - 1.0 / m)))

        # Gauss inverse formula V^{-1}=H^{-1} V^T W.
        h_diag = 2.0 / (2.0 * np.arange(degree + 1) + 1.0)
        explicit_v_inv = np.diag(1.0 / h_diag) @ vander.T @ np.diag(weights)
        gauss_inverse_error = float(
            np.max(np.abs(explicit_v_inv - np.linalg.inv(vander)))
        )

        # The weighted singular-value identity from the report.
        b_weighted = b_matrix @ np.diag(1.0 / np.sqrt(weights))
        d_weighted = d_matrix @ np.diag(1.0 / np.sqrt(h_diag))
        singular_b = np.linalg.svd(b_weighted, compute_uv=False)
        singular_d = np.linalg.svd(d_weighted, compute_uv=False)
        weighted_singular_error = float(np.max(np.abs(singular_b - singular_d)))

        # Vandermonde--Appell moment transmutation through degree d.
        moment_error = 0.0
        a_polys = appell_polynomials(degree)
        a_values = evaluate_symbolic_polys(a_polys, centers)
        for r in range(degree + 1):
            left = b_matrix @ (nodes**r)
            right = a_values[:, r] / m
            moment_error = max(moment_error, float(np.max(np.abs(left - right))))

        rows.append(
            {
                "degree": degree,
                "M": m,
                "atoms": len(shifts),
                "max_UB_minus_I": identity_error,
                "max_UD_minus_V": legendre_error,
                "max_P2_minus_P": projector_error,
                "trace_error": trace_error,
                "row_sum_error": row_sum_error,
                "gauss_inverse_error": gauss_inverse_error,
                "weighted_singular_error": weighted_singular_error,
                "moment_transmutation_error": moment_error,
                "norm_B_weighted_2": spectral_norm(b_weighted),
                "norm_D_weighted_2": spectral_norm(d_weighted),
                "smallest_singular_U": smallest_nonzero_singular_value(u_matrix),
                "max_column_l1_B": float(np.max(np.sum(np.abs(b_matrix), axis=0))),
            }
        )

    csv_path = output_dir / "matrix_checks.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def chebyshev_lobatto_nodes(degree: int) -> np.ndarray:
    if degree == 0:
        return np.array([0.0])
    nodes = np.cos(np.pi * np.arange(degree + 1) / degree)
    return np.sort(nodes)


def run_interpolation_checks(
    output_dir: Path,
    up: UpFFT,
    q_polys: Sequence[sp.Expr],
    degrees: Iterable[int],
) -> list[dict[str, float | int]]:
    evaluation = np.linspace(-1.0, 1.0, 1201)
    up_values = up(evaluation)
    rows: list[dict[str, float | int]] = []

    for degree in degrees:
        nodes = chebyshev_lobatto_nodes(degree)
        values = up(nodes)
        vander = np.polynomial.legendre.legvander(nodes, degree)
        legendre_coeffs = np.linalg.solve(vander, values)
        direct = np.polynomial.legendre.legval(evaluation, legendre_coeffs)

        m, shifts = lattice_indices(degree)
        centers = shifts / m
        q_values = evaluate_symbolic_polys(q_polys[: degree + 1], centers)
        d_matrix = q_values / m
        atom_coeffs = d_matrix @ legendre_coeffs

        # Reconstruct on a coarser grid; exact arithmetic would match direct.
        reconstruction_grid = np.linspace(-1.0, 1.0, 401)
        reconstructed = reconstruct_from_atoms(
            reconstruction_grid, centers, atom_coeffs, up, chunk_size=64
        )
        direct_on_reconstruction_grid = np.polynomial.legendre.legval(
            reconstruction_grid, legendre_coeffs
        )

        rows.append(
            {
                "degree": degree,
                "M": m,
                "atoms": len(shifts),
                "interpolation_max_error": float(np.max(np.abs(direct - up_values))),
                "floating_atomization_max_error": float(
                    np.max(np.abs(reconstructed - direct_on_reconstruction_grid))
                ),
                "atom_coeff_l1": float(np.sum(np.abs(atom_coeffs))),
                "atom_coeff_linf": float(np.max(np.abs(atom_coeffs))),
            }
        )

    csv_path = output_dir / "interpolation_errors.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows



def up_pole_constant(dps: int = 80) -> mp.mpf:
    """Return C=M(pi*i)=prod_{j>=1} sinc(1/2^j) at high precision."""
    mp.mp.dps = dps
    product = mp.mpf(1)
    for j in range(1, 240):
        y = mp.pi / (mp.mpf(2) ** j)
        product *= mp.sin(y) / y
    return product


def run_block_instability_checks(
    output_dir: Path, q_polys: Sequence[sp.Expr], max_block: int = 6
) -> list[dict[str, float | int]]:
    """Measure atomwise variation in the termwise Legendre closure.

    The n-th closed-loop block is

        (u_n/4^n) sum_{|k|<2*4^n} Q_{2n}(k/4^n) up(x-k/4^n).

    As a function this is merely u_n P_{2n}(x), but its raw coefficient
    variation can be much larger.  The k=0 coefficient is singled out because
    the same central atom up(x) occurs in every block.
    """
    u_coeffs = exact_up_legendre_coefficients(max_block)
    constant_c = up_pole_constant(80)
    rows: list[dict[str, float | int]] = []
    for n in range(max_block + 1):
        m = 4**n
        shifts = np.arange(-2 * m + 1, 2 * m, dtype=np.int64)
        q_poly = q_polys[2 * n]
        q_values = np.polyval(polynomial_to_numpy(q_poly), shifts / m)
        coefficient_scale = abs(float(u_coeffs[n])) / m
        central_q = float(q_poly.subs(X, 0))
        central_coefficient = float(u_coeffs[n]) * central_q / m
        if n == 0:
            leading_asymptotic = float("nan")
            asymptotic_ratio = float("nan")
        else:
            leading_asymptotic = float(
                2
                * ((-1) ** n)
                / constant_c
                * mp.factorial(4 * n)
                / (mp.factorial(2 * n) * (4 * mp.pi) ** (2 * n))
            )
            asymptotic_ratio = central_q / leading_asymptotic
        rows.append(
            {
                "block_index_n": n,
                "M": m,
                "atoms": len(shifts),
                "u_n": float(u_coeffs[n]),
                "Q_2n_at_zero": central_q,
                "leading_Q_asymptotic": leading_asymptotic,
                "Q_asymptotic_ratio": asymptotic_ratio,
                "central_atom_coefficient": central_coefficient,
                "block_coefficient_l1": coefficient_scale * float(np.sum(np.abs(q_values))),
                "max_abs_Q_on_lattice": float(np.max(np.abs(q_values))),
            }
        )

    with (output_dir / "block_instability.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def run_q_origin_asymptotics(output_dir: Path, max_n: int = 50) -> list[dict[str, str | int]]:
    """High-precision check of the new asymptotic for Q_{2n}(0).

    Reciprocal-MGF coefficients are generated from cumulants in exponential
    form.  The Legendre constant term is then evaluated directly from the
    exact finite coefficient formula, avoiding construction of huge symbolic
    polynomials.
    """
    mp.mp.dps = 100
    maximum_order = 2 * max_n
    kappa = [mp.mpf(0)] * (maximum_order + 1)
    for r in range(1, max_n + 1):
        kappa[2 * r] = mp.bernoulli(2 * r) / (
            mp.mpf(2 * r) * (1 - mp.power(4, -r))
        )

    gamma = [mp.mpf(0)] * (maximum_order + 1)
    gamma[0] = mp.mpf(1)
    # If G(z)=exp(-K(z)) in exponential generating convention, then
    # gamma_{n+1}=-sum_{k=0}^n binom(n,k) kappa_{k+1} gamma_{n-k}.
    for n in range(maximum_order):
        gamma[n + 1] = -mp.fsum(
            mp.binomial(n, k) * kappa[k + 1] * gamma[n - k]
            for k in range(n + 1)
            if kappa[k + 1] != 0
        )

    constant_c = up_pole_constant(100)
    sample_indices = sorted(set([1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 30, 40, max_n]))
    rows: list[dict[str, str | int]] = []
    for n in sample_indices:
        q0 = mp.fsum(
            mp.power(2, -2 * n)
            * ((-1) ** j)
            * mp.factorial(4 * n - 2 * j)
            / (
                mp.factorial(j)
                * mp.factorial(2 * n - j)
                * mp.factorial(2 * n - 2 * j)
            )
            * gamma[2 * n - 2 * j]
            for j in range(n + 1)
        )
        leading_gamma_term = (
            mp.power(2, -2 * n) * mp.binomial(4 * n, 2 * n) * gamma[2 * n]
        )
        leading_pole_asymptotic = (
            2
            * ((-1) ** n)
            / constant_c
            * mp.factorial(4 * n)
            / (mp.factorial(2 * n) * (4 * mp.pi) ** (2 * n))
        )
        rows.append(
            {
                "n": n,
                "Q_2n_at_zero": mp.nstr(q0, 24),
                "ratio_to_highest_derivative_term": mp.nstr(q0 / leading_gamma_term, 18),
                "ratio_to_pole_asymptotic": mp.nstr(q0 / leading_pole_asymptotic, 18),
                "root_ratio": mp.nstr(
                    abs(q0) ** (mp.mpf(1) / (2 * n))
                    / (mp.mpf(2 * n) / (mp.pi * mp.e)),
                    18,
                ),
            }
        )

    with (output_dir / "q_origin_asymptotics.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows

def write_symbolic_tables(output_dir: Path, max_degree: int = 10) -> None:
    gamma = reciprocal_coefficients(max_degree)
    appells = appell_polynomials(max_degree)
    q_polys = deconvolved_legendre_polynomials(max_degree)
    u_coeffs = exact_up_legendre_coefficients(max_degree // 2)

    with (output_dir / "symbolic_data.txt").open("w", encoding="utf-8") as handle:
        handle.write("Reciprocal-MGF coefficients gamma_n\n")
        for n, value in enumerate(gamma):
            handle.write(f"gamma_{n} = {value}\n")
        handle.write("\nRvachev--Appell polynomials A_n(x)\n")
        for n, value in enumerate(appells):
            handle.write(f"A_{n}(x) = {value}\n")
        handle.write("\nDeconvolved Legendre polynomials Q_n(x)\n")
        for n, value in enumerate(q_polys):
            handle.write(f"Q_{n}(x) = {value}\n")
        handle.write("\nExact Fourier--Legendre coefficients u_n\n")
        for n, value in enumerate(u_coeffs):
            handle.write(f"u_{n} = {value}\n")

    with (output_dir / "low_degree_polynomials.tex").open("w", encoding="utf-8") as handle:
        handle.write("% Generated by experiments.py\n")
        handle.write("\\begin{align*}\n")
        for n in range(min(6, len(appells))):
            end = "\\\\\n" if n < min(6, len(appells)) - 1 else "\n"
            handle.write(f"A_{n}(x)&={sp.latex(appells[n])}{end}")
        handle.write("\\end{align*}\n")
        handle.write("\\begin{align*}\n")
        for n in range(min(6, len(q_polys))):
            end = "\\\\\n" if n < min(6, len(q_polys)) - 1 else "\n"
            handle.write(f"Q_{n}(x)&={sp.latex(q_polys[n])}{end}")
        handle.write("\\end{align*}\n")

    with (output_dir / "legendre_coefficients.tex").open("w", encoding="utf-8") as handle:
        handle.write("% Generated by experiments.py\n")
        handle.write("\\begin{tabular}{@{}rll@{}}\n\\toprule\n")
        handle.write("$n$ & exact $u_n$ & decimal value \\\\\n\\midrule\n")
        for n, value in enumerate(u_coeffs):
            handle.write(f"{n} & ${sp.latex(value)}$ & ${float(value):.12g}$ \\\\\n")
        handle.write("\\bottomrule\n\\end{tabular}\n")


def make_plots(
    output_dir: Path,
    up: UpFFT,
    q_polys: Sequence[sp.Expr],
    matrix_rows: Sequence[dict[str, float | int]],
    interpolation_rows: Sequence[dict[str, float | int]],
    block_rows: Sequence[dict[str, float | int]],
) -> None:
    import matplotlib.pyplot as plt

    # 1. One Gauss cardinal polynomial and its exact atomization (numerically evaluated).
    degree = 4
    (
        nodes,
        weights,
        m,
        shifts,
        centers,
        u_matrix,
        vander,
        d_matrix,
        b_matrix,
    ) = gauss_matrices(degree, up, q_polys)
    cardinal_index = degree // 2
    evaluation = np.linspace(-1.0, 1.0, 1201)
    v_inv = np.linalg.inv(vander)
    true_cardinal = np.polynomial.legendre.legval(
        evaluation, v_inv[:, cardinal_index]
    )
    reconstruction = reconstruct_from_atoms(
        evaluation, centers, b_matrix[:, cardinal_index], up, chunk_size=96
    )

    plt.figure(figsize=(7.2, 4.4))
    plt.plot(evaluation, true_cardinal, label="Lagrange cardinal polynomial")
    plt.plot(evaluation, reconstruction, linestyle="--", label="finite up-shift sum")
    plt.scatter(nodes, np.eye(degree + 1)[:, cardinal_index], s=24, label="cardinal data")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Degree-4 Gauss cardinal and its finite Rvachev-up synthesis")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "cardinal_reconstruction.png", dpi=190)
    plt.close()

    plt.figure(figsize=(7.2, 4.2))
    plt.semilogy(evaluation, np.maximum(np.abs(reconstruction - true_cardinal), 1e-18))
    plt.xlabel("x")
    plt.ylabel("absolute error")
    plt.title("Floating-point residual of the exact cardinal identity")
    plt.tight_layout()
    plt.savefig(output_dir / "cardinal_reconstruction_error.png", dpi=190)
    plt.close()

    # 2. Exact Legendre partial sums of up.
    u_coeffs = exact_up_legendre_coefficients(8)
    x_plot = np.linspace(-1.0, 1.0, 1601)
    plt.figure(figsize=(7.2, 4.4))
    plt.plot(x_plot, up(x_plot), linewidth=2.0, label="up(x)")
    for truncation in (1, 2, 4, 8):
        coeff = np.zeros(2 * truncation + 1)
        for n in range(truncation + 1):
            coeff[2 * n] = float(u_coeffs[n])
        partial = np.polynomial.legendre.legval(x_plot, coeff)
        plt.plot(x_plot, partial, label=f"Legendre S_{truncation}")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Fourier--Legendre partial sums used in the closed loop")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "legendre_partial_sums.png", dpi=190)
    plt.close()

    # 3. Conditioning growth.
    degrees = np.array([int(row["degree"]) for row in matrix_rows])
    bnorm = np.array([float(row["norm_B_weighted_2"]) for row in matrix_rows])
    l1norm = np.array([float(row["max_column_l1_B"]) for row in matrix_rows])
    plt.figure(figsize=(7.2, 4.4))
    plt.semilogy(degrees, bnorm, marker="o", label=r"$\|B W^{-1/2}\|_2$")
    plt.semilogy(degrees, l1norm, marker="s", label="maximum column l1 norm")
    plt.xlabel("polynomial degree d")
    plt.ylabel("coefficient amplification")
    plt.title("Growth of the exact Lagrange-to-up synthesis operator")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "conditioning_growth.png", dpi=190)
    plt.close()

    # 4. Approximation error versus floating-point atomization residual.
    idegrees = np.array([int(row["degree"]) for row in interpolation_rows])
    interp_error = np.array(
        [float(row["interpolation_max_error"]) for row in interpolation_rows]
    )
    atom_error = np.array(
        [float(row["floating_atomization_max_error"]) for row in interpolation_rows]
    )
    plt.figure(figsize=(7.2, 4.4))
    plt.semilogy(idegrees, interp_error, marker="o", label="Chebyshev interpolation error")
    plt.semilogy(idegrees, atom_error, marker="s", label="floating atomization residual")
    plt.xlabel("polynomial degree d")
    plt.ylabel("maximum error")
    plt.title("Approximation improves while exact atomization becomes ill-conditioned")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "approximation_vs_roundoff.png", dpi=190)
    plt.close()

    # 5. Raw variation of the termwise closed-loop blocks.
    bindices = np.array([int(row["block_index_n"]) for row in block_rows])
    bvariation = np.array([float(row["block_coefficient_l1"]) for row in block_rows])
    bcentral = np.array([abs(float(row["central_atom_coefficient"])) for row in block_rows])
    plt.figure(figsize=(7.2, 4.4))
    plt.semilogy(bindices, bvariation, marker="o", label="block coefficient l1 variation")
    plt.semilogy(bindices, np.maximum(bcentral, 1e-18), marker="s", label="absolute central-atom coefficient")
    plt.xlabel("Legendre block index n")
    plt.ylabel("raw coefficient magnitude")
    plt.title("Large internal cancellation in the closed up-function loop")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "closed_loop_block_variation.png", dpi=190)
    plt.close()


def write_readme(output_dir: Path) -> None:
    text = """Reproducibility notes
=====================

Run all exact checks, numerical tables, and figures:

    python experiments.py

Run checks and tables without plotting:

    python experiments.py --no-plots

The up-function evaluator uses the repository Fourier convention

    Phi(xi) = product_{j>=0} sinc(pi*xi/2^j)

and an inverse FFT on a period-8 grid.  The strongly cancellation-prone
minimal endpoint-dictionary verification is instead performed at 80 decimal
digits using the exact odd-half-integer cosine series and 3000 terms.

Files generated by the script
-----------------------------
- matrix_checks.csv: U B=I, U D=V, projector, moment, and weighted-SVD checks.
- interpolation_errors.csv: approximation error and floating-point cancellation.
- block_instability.csv: raw l1 variation and central coefficients of closed-loop blocks.
- q_origin_asymptotics.csv: 100-digit verification of the Q_{2n}(0) asymptotic.
- endpoint_compression_certificate.txt: exact d=4 matrix and 80-digit check.
- symbolic_data.txt: gamma_n, Appell A_n, deconvolved Legendre Q_n, exact u_n.
- *.tex snippets: exact low-degree formulae used by the report.
- *.png: reconstruction, partial sums, conditioning, and roundoff figures.

The identities are exact symbolically.  Reported floating residuals measure only
the FFT/interpolation truncation and finite-precision cancellation.
"""
    (output_dir / "README.txt").write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-plots", action="store_true", help="skip matplotlib figures")
    parser.add_argument(
        "--output-dir",
        default=None,
        help="directory for outputs (default: directory containing this script)",
    )
    args = parser.parse_args()

    output_dir = Path(args.output_dir) if args.output_dir else Path(__file__).resolve().parent
    output_dir.mkdir(parents=True, exist_ok=True)

    max_degree = 12
    q_polys = deconvolved_legendre_polynomials(max_degree)
    write_symbolic_tables(output_dir, max_degree=10)

    up = UpFFT(grid_power=19, period=8.0, factors=42)
    diagnostics = up.diagnostics()
    (output_dir / "fft_diagnostics.txt").write_text(
        "\n".join(f"{key} = {value:.17g}" for key, value in diagnostics.items()) + "\n",
        encoding="utf-8",
    )

    matrix_rows = run_matrix_checks(output_dir, up, q_polys, degrees=range(1, 11))
    interpolation_rows = run_interpolation_checks(
        output_dir, up, q_polys, degrees=(2, 4, 6, 8, 10, 12)
    )
    block_rows = run_block_instability_checks(output_dir, q_polys, max_block=6)
    run_q_origin_asymptotics(output_dir, max_n=50)
    endpoint_summary = verify_endpoint_compression(output_dir)

    if not args.no_plots:
        make_plots(output_dir, up, q_polys, matrix_rows, interpolation_rows, block_rows)

    write_readme(output_dir)

    print("FFT diagnostics:", diagnostics)
    print("largest matrix residual:", max(row["max_UB_minus_I"] for row in matrix_rows))
    print("endpoint compression:", endpoint_summary)
    print("outputs written to", output_dir)


if __name__ == "__main__":
    main()
