#!/usr/bin/env python3
"""Exact local polynomial representation by finite sums of Rvachev up atoms.

This script accompanies the report

    Exact Polynomial Windows from Finite Sums of Shifted and Scaled
    Rvachev up Functions

The symbolic part uses exact SymPy arithmetic.  It implements:

* cumulants and moments of the Rvachev up density;
* the associated monic Appell polynomials A_n;
* coefficients of the reciprocal moment-generating function;
* restricted binary partition numbers p_m(N);
* the exact arbitrary-interval representation theorem;
* the two-atoms-per-degree specialization h=(b-a)/2;
* symbolic verification of the polynomial identity;
* an independent numerical check based on Fourier inversion of the
  infinite sinc product.

Mathematical normalization
--------------------------
The Rvachev function u=up is supported on [-1,1], integrates to one, and
has characteristic function

    phi(t) = product_{j>=1} sinc(t/2^j),

where sinc(z)=sin(z)/z.  An atom is u((x-center)/scale); the scale factor
is intentionally *not* included in front of the atom, because that is the
normalization used in the representation theorem.

Dependencies: sympy, numpy, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
import sympy as sp


@dataclass(frozen=True)
class UpAtom:
    """One term amplitude * up((x-center)/scale).

    Attributes
    ----------
    degree:
        Appell/basis level n from which the atom originates.
    partition_index:
        The binary-partition index N.  In the sparse two-atom formula it
        is 0 or 1.
    amplitude, center, scale:
        Exact SymPy expressions whenever the input data are exact.
    """

    degree: int
    partition_index: int
    amplitude: sp.Expr
    center: sp.Expr
    scale: sp.Expr


def rvachev_cumulants(order: int) -> list[sp.Expr]:
    """Return cumulants kappa_0,...,kappa_order of the up density.

    For m>=1,

        kappa_{2m} = 2^(2m-1) B_{2m} / (m (2^(2m)-1)),
        kappa_{2m+1} = 0.

    kappa_0 is set to zero for convenient indexing.
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    kappa: list[sp.Expr] = [sp.Integer(0)] * (order + 1)
    for r in range(2, order + 1, 2):
        m = r // 2
        kappa[r] = sp.factor(
            sp.Integer(2) ** (2 * m - 1)
            * sp.bernoulli(2 * m)
            / (sp.Integer(m) * (sp.Integer(2) ** (2 * m) - 1))
        )
    return kappa


def moments_from_cumulants(kappa: Sequence[sp.Expr]) -> list[sp.Expr]:
    """Convert cumulants into moments by the complete-Bell recurrence."""

    order = len(kappa) - 1
    mu: list[sp.Expr] = [sp.Integer(0)] * (order + 1)
    mu[0] = sp.Integer(1)
    for n in range(1, order + 1):
        mu[n] = sp.factor(
            sum(
                sp.binomial(n - 1, r - 1) * kappa[r] * mu[n - r]
                for r in range(1, n + 1)
            )
        )
    return mu


def rvachev_moments(order: int) -> list[sp.Expr]:
    """Return exact moments mu_n=integral z^n up(z) dz, 0<=n<=order."""

    return moments_from_cumulants(rvachev_cumulants(order))


def reciprocal_mgf_coefficients(order: int) -> list[sp.Expr]:
    r"""Return gamma_n in 1/M(t)=sum gamma_n t^n/n!.

    Here M(t)=E exp(tZ), where Z has density up.  Since

        log(1/M(t)) = -sum kappa_n t^n/n!,

    the coefficients are complete Bell polynomials in the negated
    cumulants.  The recurrence below avoids any series truncation issues.
    """

    kappa = rvachev_cumulants(order)
    gamma: list[sp.Expr] = [sp.Integer(0)] * (order + 1)
    gamma[0] = sp.Integer(1)
    for n in range(1, order + 1):
        gamma[n] = sp.factor(
            -sum(
                sp.binomial(n - 1, r - 1) * kappa[r] * gamma[n - r]
                for r in range(1, n + 1)
            )
        )
    return gamma


def appell_polynomials(order: int, variable: sp.Symbol | None = None) -> list[sp.Expr]:
    r"""Return the monic Appell family A_0,...,A_order.

    A_n(y)=E[(y-Z)^n].  The density is symmetric, so this equals
    E[(y+Z)^n], and therefore

        A_n(y)=sum_{r=0}^n binomial(n,r) mu_r y^(n-r).
    """

    if variable is None:
        variable = sp.Symbol("y")
    mu = rvachev_moments(order)
    return [
        sp.expand(
            sum(
                sp.binomial(n, r) * mu[r] * variable ** (n - r)
                for r in range(n + 1)
            )
        )
        for n in range(order + 1)
    ]


def restricted_binary_partitions(m: int, maximum: int) -> list[int]:
    r"""Return p_m(N), 0<=N<=maximum.

    p_m(N) counts nonnegative integer solutions of

        N = k_0 + 2 k_1 + ... + 2^(m-1) k_{m-1},

    equivalently

        sum_N p_m(N) z^N = product_{j=0}^{m-1}(1-z^(2^j))^(-1).

    A standard unbounded-knapsack dynamic program computes all numbers in
    O(m*maximum) integer operations.
    """

    if m <= 0:
        raise ValueError("m must be positive")
    if maximum < 0:
        raise ValueError("maximum must be nonnegative")
    values = [0] * (maximum + 1)
    values[0] = 1
    for j in range(m):
        part = 1 << j
        for n in range(part, maximum + 1):
            values[n] += values[n - part]
    return values


def _as_exact(value: sp.Expr | int | float | str) -> sp.Expr:
    """Convert common numeric input to a SymPy expression.

    Floats are converted from their decimal string, rather than from their
    binary expansion, so 0.5 becomes exactly 1/2.
    """

    if isinstance(value, float):
        return sp.Rational(str(value))
    return sp.sympify(value)


def appell_basis_coefficients(
    polynomial: sp.Expr,
    x: sp.Symbol,
    a: sp.Expr,
    b: sp.Expr,
    h: sp.Expr | None = None,
) -> tuple[list[sp.Expr], list[sp.Expr], sp.Expr, sp.Expr]:
    """Express a polynomial in the up-associated Appell basis.

    Let c=a-h and y=(x-c)/h.  This routine returns b_n such that

        p(x) = sum_{n=0}^d b_n A_n(y).

    It also returns the list A_n, c, and h.  The coefficient transform is

        q(y) = (1/M)(D) p(c+h y),
        b_n = [y^n] q(y).
    """

    a = _as_exact(a)
    b = _as_exact(b)
    if sp.simplify(b - a) <= 0:
        raise ValueError("the interval must satisfy b>a")
    if h is None:
        h = sp.simplify((b - a) / 2)
    h = _as_exact(h)
    if h <= 0:
        raise ValueError("h must be positive")

    p = sp.Poly(sp.expand(polynomial), x, domain="EX")
    degree = p.degree()
    if degree < 0:
        degree = 0
    c = sp.simplify(a - h)
    y = sp.Symbol("y")
    transformed = sp.expand(p.as_expr().subs(x, c + h * y))

    gamma = reciprocal_mgf_coefficients(degree)
    q = sp.expand(
        sum(
            gamma[r] * sp.diff(transformed, y, r) / sp.factorial(r)
            for r in range(degree + 1)
        )
    )
    q_poly = sp.Poly(q, y, domain="EX")
    coefficients = [sp.factor(q_poly.nth(n)) for n in range(degree + 1)]
    appell = appell_polynomials(degree, y)

    residual = sp.expand(
        transformed - sum(coefficients[n] * appell[n] for n in range(degree + 1))
    )
    if residual != 0:
        raise ArithmeticError(f"Appell transform verification failed: {residual}")
    return coefficients, appell, c, h



def representation_atoms(
    polynomial: sp.Expr,
    x: sp.Symbol,
    a: sp.Expr,
    b: sp.Expr,
    h: sp.Expr | None = None,
) -> tuple[list[UpAtom], list[sp.Expr]]:
    r"""Construct the exact finite up-atom representation on [a,b].

    With K=ceil((b-a)/(2h)), the theorem gives

      p(x) = sum_{n=0}^d sum_{N=0}^K alpha_{n,N}
             up((x-C_{n,N})/H_n),     x in [a,b],

    where

      alpha_{n,N} = b_n n! 2^(n(n+1)/2) p_{n+1}(N),
      C_{n,N}     = a+h(2^(n+1)-2+2N),
      H_n         = 2^(n+1) h.

    The returned basis coefficients b_n are exact SymPy expressions.
    """

    a = _as_exact(a)
    b = _as_exact(b)
    coefficients, _, _, h_exact = appell_basis_coefficients(polynomial, x, a, b, h)
    length = sp.simplify(b - a)
    ratio = sp.simplify(length / (2 * h_exact))
    # ceiling() is exact for rational/algebraic numeric input; force to int.
    K_expr = sp.ceiling(ratio)
    if not K_expr.is_integer:
        raise ValueError("ceil((b-a)/(2h)) could not be evaluated exactly")
    K = int(K_expr)

    atoms: list[UpAtom] = []
    for n, basis_coefficient in enumerate(coefficients):
        partitions = restricted_binary_partitions(n + 1, K)
        common = sp.factor(
            basis_coefficient
            * sp.factorial(n)
            * sp.Integer(2) ** (n * (n + 1) // 2)
        )
        scale = sp.factor(sp.Integer(2) ** (n + 1) * h_exact)
        for N, count in enumerate(partitions):
            amplitude = sp.factor(common * count)
            center = sp.factor(
                a + h_exact * (sp.Integer(2) ** (n + 1) - 2 + 2 * N)
            )
            atoms.append(UpAtom(n, N, amplitude, center, scale))
    return atoms, coefficients


def symbolic_basis_identity(
    polynomial: sp.Expr,
    x: sp.Symbol,
    a: sp.Expr,
    b: sp.Expr,
    h: sp.Expr | None = None,
) -> sp.Expr:
    """Return the exact polynomial-side residual (always zero on success).

    The compactly supported atoms themselves are not represented as SymPy
    elementary functions.  Instead, this verifies the theorem through the
    proven identity between each truncated atom block and A_n on [a,b].
    """

    coefficients, appell, c, h_exact = appell_basis_coefficients(
        polynomial, x, a, b, h
    )
    y = next(iter(appell[0].free_symbols), sp.Symbol("y"))
    # appell[0] has no free symbol, so obtain y from A_1 if available.
    if len(appell) > 1 and appell[1].free_symbols:
        y = next(iter(appell[1].free_symbols))
    transformed = sp.expand(sp.sympify(polynomial).subs(x, c + h_exact * y))
    return sp.expand(
        transformed - sum(coefficients[n] * appell[n] for n in range(len(coefficients)))
    )


def fourier_up_grid(
    grid_power: int = 19,
    period: float = 4.0,
    sinc_factors: int = 44,
) -> tuple[np.ndarray, np.ndarray]:
    r"""Approximate up on a uniform grid by the infinite sinc product.

    The period must exceed the support length 2.  The periodic Fourier
    coefficients are phi(2*pi*k/period)/period, where

        phi(t)=product_{j>=1} sinc(t/2^j).

    Truncating the product after `sinc_factors` and applying an inverse FFT
    gives a spectrally accurate independent numerical approximation.  The
    returned grid is ordered on [-period/2, period/2).
    """

    if grid_power < 8:
        raise ValueError("grid_power is too small for a useful check")
    if period <= 2.0:
        raise ValueError("period must exceed the support length 2")
    if sinc_factors <= 0:
        raise ValueError("sinc_factors must be positive")

    count = 1 << grid_power
    spacing = period / count
    omega = 2.0 * math.pi * np.fft.fftfreq(count, d=spacing)
    phi = np.ones(count, dtype=np.float64)
    for j in range(1, sinc_factors + 1):
        # np.sinc(z)=sin(pi*z)/(pi*z), hence z=(omega/2^j)/pi.
        phi *= np.sinc(omega / ((1 << j) * math.pi))
    values_zero_origin = (count / period) * np.fft.ifft(phi).real
    values = np.fft.fftshift(values_zero_origin)
    grid = (np.arange(count) - count // 2) * spacing
    # Tiny transform roundoff outside support is not mathematically real.
    values[np.abs(grid) >= 1.0] = 0.0
    return grid, values


def interpolate_up(
    arguments: np.ndarray,
    grid: np.ndarray,
    values: np.ndarray,
) -> np.ndarray:
    """Interpolate the FFT grid, enforcing the exact compact support."""

    arguments = np.asarray(arguments, dtype=float)
    result = np.zeros_like(arguments)
    inside = np.abs(arguments) < 1.0
    result[inside] = np.interp(arguments[inside], grid, values)
    return result


def evaluate_atom_sum(
    points: np.ndarray,
    atoms: Iterable[UpAtom],
    up_grid: np.ndarray,
    up_values: np.ndarray,
) -> np.ndarray:
    """Numerically evaluate a finite atom list at real points."""

    points = np.asarray(points, dtype=float)
    total = np.zeros_like(points)
    # Pairwise-by-level accumulation would be preferable at very high
    # degree.  For the modest reproducibility examples here, ordinary
    # accumulation is sufficient and makes the code transparent.
    for atom in atoms:
        amplitude = float(sp.N(atom.amplitude, 18))
        center = float(sp.N(atom.center, 18))
        scale = float(sp.N(atom.scale, 18))
        total += amplitude * interpolate_up((points - center) / scale, up_grid, up_values)
    return total


def write_atom_table(path: Path, atoms: Sequence[UpAtom]) -> None:
    """Write an exact CSV table of the constructed atoms."""

    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["degree", "partition_index", "amplitude", "center", "scale"])
        for atom in atoms:
            writer.writerow(
                [
                    atom.degree,
                    atom.partition_index,
                    sp.sstr(atom.amplitude),
                    sp.sstr(atom.center),
                    sp.sstr(atom.scale),
                ]
            )


def run_quartic_demo(output_directory: Path, quick: bool = False) -> dict[str, object]:
    """Reproduce the report's exact and numerical quartic example."""

    output_directory.mkdir(parents=True, exist_ok=True)
    x = sp.Symbol("x")
    polynomial = 3 * x**4 - 2 * x**3 + 5 * x - 7
    a = sp.Integer(0)
    b = sp.Integer(1)
    h = sp.Rational(1, 2)

    atoms, coefficients = representation_atoms(polynomial, x, a, b, h)
    exact_residual = symbolic_basis_identity(polynomial, x, a, b, h)
    if exact_residual != 0:
        raise ArithmeticError(f"nonzero symbolic residual: {exact_residual}")

    table_path = output_directory / "quartic_atoms.csv"
    write_atom_table(table_path, atoms)

    grid_power = 17 if quick else 20
    grid, values = fourier_up_grid(grid_power=grid_power, period=4.0, sinc_factors=44)
    points = np.linspace(0.0, 1.0, 1001)
    target = 3 * points**4 - 2 * points**3 + 5 * points - 7
    reconstructed = evaluate_atom_sum(points, atoms, grid, values)
    residual = reconstructed - target
    max_error = float(np.max(np.abs(residual)))
    rms_error = float(np.sqrt(np.mean(residual**2)))

    sample_path = output_directory / "quartic_numerical_check.csv"
    with sample_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["x", "polynomial", "up_atom_sum", "residual"])
        for row in zip(points, target, reconstructed, residual, strict=True):
            writer.writerow([f"{value:.17g}" for value in row])

    plt.figure(figsize=(7.2, 4.5))
    plt.plot(points, target, label="polynomial")
    plt.plot(points, reconstructed, linestyle="--", label="finite up sum")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Exact quartic window: independent numerical evaluation")
    plt.legend()
    plt.tight_layout()
    reconstruction_plot = output_directory / "quartic_reconstruction.png"
    plt.savefig(reconstruction_plot, dpi=180)
    plt.close()

    plt.figure(figsize=(7.2, 4.0))
    plt.plot(points, residual)
    plt.xlabel("x")
    plt.ylabel("finite-sum value minus polynomial")
    plt.title("Numerical residual (FFT sinc-product evaluation of up)")
    plt.tight_layout()
    residual_plot = output_directory / "quartic_residual.png"
    plt.savefig(residual_plot, dpi=180)
    plt.close()

    results = {
        "polynomial": polynomial,
        "basis_coefficients": coefficients,
        "atoms": atoms,
        "symbolic_residual": exact_residual,
        "max_error": max_error,
        "rms_error": rms_error,
        "grid_power": grid_power,
        "sinc_factors": 44,
        "table_path": table_path,
        "sample_path": sample_path,
        "reconstruction_plot": reconstruction_plot,
        "residual_plot": residual_plot,
    }

    summary_path = output_directory / "numerical_summary.txt"
    with summary_path.open("w", encoding="utf-8") as handle:
        handle.write("Quartic exact-window reproducibility summary\n")
        handle.write("===========================================\n")
        handle.write(f"p(x) = {sp.sstr(polynomial)}\n")
        handle.write(f"interval = [{a}, {b}], h = {h}\n")
        handle.write(f"Appell coefficients b_n = {[sp.sstr(v) for v in coefficients]}\n")
        handle.write(f"symbolic Appell residual = {exact_residual}\n")
        handle.write(f"FFT grid = 2^{grid_power}, sinc factors = 44, period = 4\n")
        handle.write(f"maximum absolute numerical residual = {max_error:.12e}\n")
        handle.write(f"RMS numerical residual = {rms_error:.12e}\n")
        handle.write("\nExact atoms (amplitude, center, scale):\n")
        for atom in atoms:
            handle.write(
                f"n={atom.degree}, N={atom.partition_index}: "
                f"({sp.sstr(atom.amplitude)}, {sp.sstr(atom.center)}, "
                f"{sp.sstr(atom.scale)})\n"
            )
    results["summary_path"] = summary_path
    return results


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Construct and verify exact polynomial windows made from Rvachev up atoms."
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("generated"),
        help="directory for CSV, plots, and numerical summary",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="use a smaller FFT grid for a faster smoke test",
    )
    args = parser.parse_args()

    result = run_quartic_demo(args.output_dir, quick=args.quick)
    print("Exact Appell coefficients:")
    for n, value in enumerate(result["basis_coefficients"]):
        print(f"  b_{n} = {value}")
    print(f"Symbolic residual: {result['symbolic_residual']}")
    print(f"Maximum numerical residual: {result['max_error']:.12e}")
    print(f"RMS numerical residual: {result['rms_error']:.12e}")
    print(f"Artifacts written under: {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
