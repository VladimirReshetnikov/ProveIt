#!/usr/bin/env python3
"""Exact and numerical experiments for the Lagrange--Rvachev loop.

This script accompanies the report
    "Lagrange Cardinal Polynomials and the Rvachev up-Function: Closing an
     Exact Finite/Infinite Representation Loop".

It performs five independent computations.

1. It constructs the moment sequence mu_n of the Rvachev density and the
   reciprocal (deconvolution) sequence gamma_n from the cumulant formula

       kappa_{2m} = 2^{2m-1} B_{2m} / (m(2^{2m}-1)).

2. For prescribed interpolation nodes xi_j, it verifies symbolically that
   every Lagrange cardinal polynomial has the exact scale-ladder expansion

       L_j(x) = sum_n b_{n,j} G_n(x+2),

   where G_n(y)=E[(y-Z)^n] and b_{n,j} is obtained by the finite differential
   operator M(D)^{-1}.  Multiplying b_{n,j} by
   n! 2^{n(n+1)/2} gives the coefficient shared by the two up-atoms in the
   nth scale-ladder block.

3. It constructs Fourier--Legendre partial sums of up from exact moments,
   applies the same triangular transform, and records the rapid growth of
   the exact atom coefficients even while the partial sums converge on
   [-1,1].  This is the numerical signature of extrapolation to the anchor
   x=-2 and of the nonanalyticity obstruction discussed in the report.

4. It compares equispaced and Chebyshev--Lobatto node sets through the
   Appell--Vandermonde matrix A_{i,n}=G_n(xi_i+2), and plots both matrix
   conditioning and the norm of the sample-to-atom transform
   diag(n!2^{n(n+1)/2}) A^{-1}.

5. It factors the exact common denominator of every Lagrange-to-atom matrix
   on rational equispaced grids, providing reproducible data for the prime-
   support theorem and the valuation problem in the report.

All symbolic identities are checked exactly over the rationals.  The plots
use floating-point arithmetic only after the exact formulas have been built.
No numerical evaluation of the up-function is required.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
import sympy as sp


X, Y, T = sp.symbols("x y t")


def rvachev_sequences(max_n: int) -> tuple[list[sp.Rational], list[sp.Rational]]:
    """Return moments mu_n and reciprocal moments gamma_n through max_n.

    The moment generating function is

        M(t) = product_{j>=1} sinh(t/2^j)/(t/2^j)
             = exp(sum_{m>=1} kappa_{2m} t^{2m}/(2m)!).

    Instead of expanding a symbolic exponential (which becomes expensive at
    moderate orders), we use the standard moment--cumulant recurrence

        a_n = sum_{k=1}^n binom(n-1,k-1) c_k a_{n-k},

    valid when A(t)=exp(sum c_k t^k/k!).  For 1/M the cumulants are simply
    -kappa_k.  The computation is exact and quadratic in max_n.
    """
    kappa = [sp.Integer(0) for _ in range(max_n + 1)]
    for m in range(1, max_n // 2 + 1):
        bernoulli = sp.bernoulli(2 * m)
        kappa[2 * m] = sp.factor(
            sp.Rational(2 ** (2 * m - 1), m * (2 ** (2 * m) - 1)) * bernoulli
        )

    def sequence_from_cumulants(sign: int) -> list[sp.Expr]:
        seq: list[sp.Expr] = [sp.Integer(0) for _ in range(max_n + 1)]
        seq[0] = sp.Integer(1)
        for n in range(1, max_n + 1):
            seq[n] = sp.factor(
                sum(
                    sp.binomial(n - 1, k - 1) * sign * kappa[k] * seq[n - k]
                    for k in range(1, n + 1)
                )
            )
        return seq

    return sequence_from_cumulants(+1), sequence_from_cumulants(-1)


def appell_polynomial(n: int, mu: Sequence[sp.Expr], variable: sp.Symbol = Y) -> sp.Expr:
    """Return G_n(variable)=sum_r binomial(n,r) mu_r variable^(n-r)."""
    return sp.expand(
        sum(sp.binomial(n, r) * mu[r] * variable ** (n - r) for r in range(n + 1))
    )


def deconvolve_polynomial(poly_in_y: sp.Expr, gamma: Sequence[sp.Expr]) -> sp.Expr:
    """Apply M(D_y)^{-1} to a polynomial, exactly."""
    degree = sp.Poly(poly_in_y, Y).degree()
    return sp.expand(
        sum(gamma[r] * sp.diff(poly_in_y, Y, r) / sp.factorial(r) for r in range(degree + 1))
    )


def lagrange_cardinals(nodes: Sequence[sp.Expr], variable: sp.Symbol = X) -> list[sp.Expr]:
    """Return cardinal polynomials L_j for distinct nodes."""
    cardinals: list[sp.Expr] = []
    for j, node_j in enumerate(nodes):
        numerator = sp.Integer(1)
        denominator = sp.Integer(1)
        for m, node_m in enumerate(nodes):
            if m == j:
                continue
            numerator *= variable - node_m
            denominator *= node_j - node_m
        cardinals.append(sp.factor(numerator / denominator))
    return cardinals


def lagrange_block_coefficients(
    cardinal: sp.Expr, degree: int, gamma: Sequence[sp.Expr]
) -> tuple[list[sp.Expr], list[sp.Expr]]:
    """Return b_n and raw two-atom amplitudes alpha_n for one cardinal.

    Set q(y)=L(y-2).  Then

        M(D)^{-1} q(y) = sum_n b_n y^n,
        alpha_n = n! 2^{n(n+1)/2} b_n.
    """
    q = sp.expand(cardinal.subs(X, Y - 2))
    deconvolved = deconvolve_polynomial(q, gamma)
    b = [sp.factor(deconvolved.coeff(Y, n)) for n in range(degree + 1)]
    alpha = [
        sp.factor(sp.factorial(n) * 2 ** (n * (n + 1) // 2) * b[n])
        for n in range(degree + 1)
    ]
    return b, alpha


def verify_lagrange_expansion(
    nodes: Sequence[sp.Expr], mu: Sequence[sp.Expr], gamma: Sequence[sp.Expr]
) -> tuple[list[sp.Expr], list[list[sp.Expr]], list[list[sp.Expr]]]:
    """Verify all cardinal expansions and the inverse-matrix identity."""
    degree = len(nodes) - 1
    cardinals = lagrange_cardinals(nodes)
    g = [appell_polynomial(n, mu, Y).subs(Y, X + 2) for n in range(degree + 1)]

    all_b: list[list[sp.Expr]] = []
    all_alpha: list[list[sp.Expr]] = []
    for cardinal in cardinals:
        b, alpha = lagrange_block_coefficients(cardinal, degree, gamma)
        residual = sp.expand(cardinal - sum(b[n] * g[n] for n in range(degree + 1)))
        if residual != 0:
            raise AssertionError(f"Nonzero exact residual: {residual}")
        all_b.append(b)
        all_alpha.append(alpha)

    # A_{i,n}=G_n(xi_i+2).  If B_{n,j}=b_{n,j}, then A B = I.
    a_matrix = sp.Matrix(
        [[appell_polynomial(n, mu, Y).subs(Y, node + 2) for n in range(degree + 1)] for node in nodes]
    )
    b_matrix = sp.Matrix(degree + 1, degree + 1, lambda n, j: all_b[j][n])
    if sp.simplify(a_matrix * b_matrix - sp.eye(degree + 1)) != sp.zeros(degree + 1):
        raise AssertionError("Appell--Vandermonde inverse identity failed")

    return cardinals, all_b, all_alpha


def legendre_coefficient(k: int, mu: Sequence[sp.Expr]) -> sp.Expr:
    """Exact Fourier--Legendre coefficient (2k+1)/2 * E[P_k(Z)]."""
    p = sp.Poly(sp.legendre(k, X), X)
    expectation = sp.Integer(0)
    for (power,), coefficient in p.terms():
        expectation += coefficient * mu[power]
    return sp.factor(sp.Rational(2 * k + 1, 2) * expectation)


def legendre_partial_sum(n_even: int, mu: Sequence[sp.Expr]) -> sp.Expr:
    """Return S_N=sum_{m=0}^N lambda_{2m} P_{2m}; n_even is N."""
    return sp.expand(
        sum(legendre_coefficient(2 * m, mu) * sp.legendre(2 * m, X) for m in range(n_even + 1))
    )


def write_csv(path: Path, rows: Iterable[Sequence[object]], header: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def latex_rational(value: sp.Expr) -> str:
    return sp.latex(sp.factor(value))


def write_tables(
    output_dir: Path,
    mu: Sequence[sp.Expr],
    gamma: Sequence[sp.Expr],
    nodes: Sequence[sp.Expr],
    cardinals: Sequence[sp.Expr],
    b: Sequence[Sequence[sp.Expr]],
    alpha: Sequence[Sequence[sp.Expr]],
) -> None:
    """Write small LaTeX fragments consumed by the main report."""
    data_dir = output_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    with (data_dir / "moment_table.tex").open("w", encoding="utf-8") as stream:
        stream.write("\\begin{tabular}{c|c|c}\n")
        stream.write("$r$ & $\\mu_r$ & $\\gamma_r$ \\\\ \\hline\n")
        for r in range(0, min(12, len(mu) - 1) + 1, 2):
            stream.write(f"{r} & ${latex_rational(mu[r])}$ & ${latex_rational(gamma[r])}$ \\\\ \n")
        stream.write("\\end{tabular}\n")

    with (data_dir / "quadratic_cardinal_table.tex").open("w", encoding="utf-8") as stream:
        stream.write("\\begin{tabular}{c|c|ccc|ccc}\n")
        stream.write(
            "$j$ & $L_j(x)$ & $b_{0j}$ & $b_{1j}$ & $b_{2j}$ "
            "& $\\alpha_{0j}$ & $\\alpha_{1j}$ & $\\alpha_{2j}$ \\\\ \\hline\n"
        )
        for j in range(len(nodes)):
            stream.write(
                f"{j} & ${sp.latex(cardinals[j])}$ & "
                + " & ".join(f"${latex_rational(v)}$" for v in b[j])
                + " & "
                + " & ".join(f"${latex_rational(v)}$" for v in alpha[j])
                + " \\\\ \n"
            )
        stream.write("\\end{tabular}\n")


def matrix_experiments(output_dir: Path, max_degree: int, mu: Sequence[sp.Expr]) -> list[tuple]:
    """Conditioning study for equispaced and Chebyshev--Lobatto nodes."""
    rows: list[tuple] = []
    for degree in range(1, max_degree + 1):
        node_sets = {
            "equispaced": np.linspace(-1.0, 1.0, degree + 1),
            "Chebyshev--Lobatto": np.sort(-np.cos(np.pi * np.arange(degree + 1) / degree)),
        }
        # Convert G_n once to efficient numerical callables.
        g_functions = [sp.lambdify(Y, appell_polynomial(n, mu, Y), "numpy") for n in range(degree + 1)]
        d_scale = np.array(
            [math.factorial(n) * 2.0 ** (n * (n + 1) / 2.0) for n in range(degree + 1)],
            dtype=float,
        )
        for name, nodes in node_sets.items():
            a = np.empty((degree + 1, degree + 1), dtype=float)
            for i, node in enumerate(nodes):
                for n, fn in enumerate(g_functions):
                    a[i, n] = float(fn(node + 2.0))
            try:
                a_inv = np.linalg.inv(a)
                cond_a = np.linalg.cond(a, 2)
                transform = d_scale[:, None] * a_inv
                norm_transform = np.linalg.norm(transform, 2)
                cond_transform = np.linalg.cond(transform, 2)
            except np.linalg.LinAlgError:
                cond_a = norm_transform = cond_transform = math.inf

            # The exact determinant formula uses only the ordinary Vandermonde.
            log10_vandermonde = 0.0
            for i in range(degree + 1):
                for j in range(i + 1, degree + 1):
                    log10_vandermonde += math.log10(abs(nodes[j] - nodes[i]))
            log10_det_transform = (
                sum(math.lgamma(n + 1) / math.log(10.0) for n in range(degree + 1))
                + math.comb(degree + 2, 3) * math.log10(2.0)
                - log10_vandermonde
            )
            rows.append(
                (
                    degree,
                    name,
                    math.log10(cond_a),
                    math.log10(norm_transform),
                    math.log10(cond_transform),
                    log10_det_transform,
                )
            )

    write_csv(
        output_dir / "data" / "node_conditioning.csv",
        rows,
        [
            "degree",
            "nodes",
            "log10_cond_A",
            "log10_norm_sample_to_atom",
            "log10_cond_sample_to_atom",
            "log10_abs_det_sample_to_atom",
        ],
    )

    for column, ylabel, filename in [
        (2, r"$\log_{10}\,\kappa_2(A)$", "appell_vandermonde_conditioning.pdf"),
        (3, r"$\log_{10}\,\|D A^{-1}\|_2$", "sample_to_atom_norm.pdf"),
    ]:
        plt.figure(figsize=(6.4, 4.2))
        for name in ("equispaced", "Chebyshev--Lobatto"):
            selected = [row for row in rows if row[1] == name]
            plt.plot([row[0] for row in selected], [row[column] for row in selected], marker="o", label=name)
        plt.xlabel("polynomial degree $d$")
        plt.ylabel(ylabel)
        plt.grid(True, alpha=0.25)
        plt.legend()
        plt.tight_layout()
        plt.savefig(output_dir / "figures" / filename)
        plt.close()

    return rows


def legendre_loop_experiments(
    output_dir: Path, max_order: int, mu: Sequence[sp.Expr], gamma: Sequence[sp.Expr]
) -> list[tuple]:
    """Build exact Legendre partial sums and transform them to up blocks."""
    rows: list[tuple] = []
    coefficient_rows: list[tuple] = []
    for order in range(max_order + 1):
        degree = 2 * order
        s_n = legendre_partial_sum(order, mu)
        q = sp.expand(s_n.subs(X, Y - 2))
        deconvolved = deconvolve_polynomial(q, gamma)
        b = [sp.factor(deconvolved.coeff(Y, n)) for n in range(degree + 1)]
        alpha = [
            sp.factor(sp.factorial(n) * 2 ** (n * (n + 1) // 2) * b[n])
            for n in range(degree + 1)
        ]

        # Exact check against the Appell basis.
        reconstruction = sp.expand(
            sum(b[n] * appell_polynomial(n, mu, X + 2) for n in range(degree + 1))
        )
        if sp.expand(s_n - reconstruction) != 0:
            raise AssertionError(f"Legendre-loop reconstruction failed for N={order}")

        # Verify the exact top-block formula from the report.  The leading
        # coefficient of P_degree is 2^{-degree}*binom(2*degree, degree).
        lambda_top = legendre_coefficient(degree, mu)
        expected_top = sp.factor(
            sp.factorial(degree)
            * 2 ** (degree * (degree + 1) // 2)
            * lambda_top
            * sp.Rational(sp.binomial(2 * degree, degree), 2**degree)
        )
        if sp.factor(alpha[degree] - expected_top) != 0:
            raise AssertionError(f"Top-block formula failed for N={order}")

        exact_abs = [abs(value) for value in alpha]
        max_index = max(range(len(alpha)), key=lambda n: exact_abs[n])
        max_alpha_exact = exact_abs[max_index]
        max_alpha_numeric = abs(sp.N(max_alpha_exact, 80))
        s_center = sp.N(s_n.subs(X, 0), 50)
        s_endpoint = sp.N(s_n.subs(X, 1), 50)
        rows.append(
            (
                order,
                degree,
                str(lambda_top),
                max_index,
                max_index == degree,
                float(sp.log(max_alpha_numeric, 10)) if max_alpha_numeric != 0 else -math.inf,
                float(s_center),
                float(s_endpoint),
            )
        )
        for n, value in enumerate(alpha):
            coefficient_rows.append((order, n, str(value), float(sp.log(abs(sp.N(value, 80)), 10)) if value else -math.inf))

    write_csv(
        output_dir / "data" / "legendre_loop_summary.csv",
        rows,
        [
            "N",
            "degree",
            "top_legendre_coefficient_exact",
            "max_block_index",
            "top_block_is_max",
            "log10_max_abs_atom_amplitude",
            "S_N_0",
            "S_N_1",
        ],
    )
    write_csv(
        output_dir / "data" / "legendre_loop_coefficients.csv",
        coefficient_rows,
        ["N", "block_index_n", "atom_amplitude_exact", "log10_abs_atom_amplitude"],
    )

    plt.figure(figsize=(6.4, 4.2))
    plt.plot([row[0] for row in rows], [row[5] for row in rows], marker="o")
    plt.xlabel("Legendre cutoff $N$ (degree $2N$)")
    plt.ylabel(r"$\log_{10}\max_n |\alpha_{n,N}|$")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(output_dir / "figures" / "legendre_loop_amplitude_growth.pdf")
    plt.close()

    plt.figure(figsize=(6.4, 4.2))
    plt.semilogy([row[0] for row in rows], [abs(row[6] - 1.0) for row in rows], marker="o", label=r"$|S_N(0)-1|$")
    plt.semilogy([row[0] for row in rows], [abs(row[7]) for row in rows], marker="s", label=r"$|S_N(1)|$")
    plt.xlabel("Legendre cutoff $N$")
    plt.ylabel("pointwise diagnostic error")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "figures" / "legendre_partial_sum_diagnostics.pdf")
    plt.close()

    return rows


def denominator_experiment(
    output_dir: Path, max_degree: int, mu: Sequence[sp.Expr], gamma: Sequence[sp.Expr]
) -> list[tuple]:
    """Record exact denominator factorizations for dyadic/equispaced nodes.

    This is exploratory data for the arithmetic conjecture in the report.
    For each degree d we use the rational equispaced grid xi_j=-1+2j/d and
    compute the least common multiple of all denominators of alpha_{n,j}.
    """
    rows: list[tuple] = []
    for degree in range(1, max_degree + 1):
        nodes = [sp.Rational(-degree + 2 * j, degree) for j in range(degree + 1)]
        _, _, alpha = verify_lagrange_expansion(nodes, mu, gamma)
        denominators = [sp.denom(value) for column in alpha for value in column]
        lcm_den = sp.ilcm(*[int(value) for value in denominators])
        factorization = sp.factorint(lcm_den)
        odd_part = 1
        for prime, exponent in factorization.items():
            if prime != 2:
                odd_part *= prime ** exponent
        rows.append((degree, lcm_den, str(factorization), odd_part))

    write_csv(
        output_dir / "data" / "amplitude_denominators.csv",
        rows,
        ["degree", "lcm_denominator", "prime_factorization", "odd_part"],
    )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--matrix-degree", type=int, default=18)
    parser.add_argument("--legendre-order", type=int, default=16)
    parser.add_argument("--denominator-degree", type=int, default=8)
    args = parser.parse_args()

    output_dir = args.output.resolve()
    (output_dir / "figures").mkdir(parents=True, exist_ok=True)
    (output_dir / "data").mkdir(parents=True, exist_ok=True)

    max_symbolic_degree = max(
        2 * args.legendre_order,
        args.matrix_degree,
        args.denominator_degree,
        12,
    )
    mu, gamma = rvachev_sequences(max_symbolic_degree)

    # Guard against a convention or recurrence regression before any larger
    # experiment is attempted.
    expected_initial = {
        "mu_0": (mu[0], sp.Integer(1)),
        "mu_2": (mu[2], sp.Rational(1, 9)),
        "mu_4": (mu[4], sp.Rational(19, 675)),
        "gamma_0": (gamma[0], sp.Integer(1)),
        "gamma_2": (gamma[2], sp.Rational(-1, 9)),
        "gamma_4": (gamma[4], sp.Rational(31, 675)),
    }
    for name, (actual, expected) in expected_initial.items():
        if sp.factor(actual - expected) != 0:
            raise AssertionError(f"{name}: expected {expected}, obtained {actual}")

    # The report's worked example uses the three nodes -1, 0, 1.
    quadratic_nodes = [sp.Integer(-1), sp.Integer(0), sp.Integer(1)]
    cardinals, b, alpha = verify_lagrange_expansion(quadratic_nodes, mu, gamma)
    write_tables(output_dir, mu, gamma, quadratic_nodes, cardinals, b, alpha)

    matrix_rows = matrix_experiments(output_dir, args.matrix_degree, mu)
    legendre_rows = legendre_loop_experiments(output_dir, args.legendre_order, mu, gamma)
    denominator_rows = denominator_experiment(output_dir, args.denominator_degree, mu, gamma)

    # Human-readable summary for reproducibility checks.
    print("Exact moment/deconvolution sequences generated through degree", max_symbolic_degree)
    print("Quadratic cardinal expansion verified exactly.")
    print("Matrix experiment rows:", len(matrix_rows))
    print("Legendre-loop cutoffs:", len(legendre_rows))
    print("Denominator experiments:", len(denominator_rows))
    print("Outputs written under", output_dir)


if __name__ == "__main__":
    main()
