#!/usr/bin/env python3
"""Numerical and symbolic experiments for the W-resummed inverse Fabius expansion.

This script accompanies the report
    inverse_fabius_asymptotics.tex

It performs four independent tasks:

1. Compute exact rational values F(2^{-n}) from the dyadic moment recurrence.
   Since F^{-1}(F(2^{-n})) = 2^{-n}, these are exceptionally clean endpoint
   test cases: no numerical inversion of F is needed.

2. Evaluate the periodic Gamma-zeta fluctuation Psi and its derivatives from
   its rapidly convergent Fourier series.

3. Compare the older square-root carrier with the principal-W/Wright-omega
   carrier developed in the report, through three correction levels.

4. Use SymPy to reconstruct the first inverse coefficients from the universal
   triangular formal equation.  This is a check on the hand derivations, not a
   hard-coded transcription of them.

The program writes CSV tables, human-readable coefficient formulae, and two
figures into the selected output directory.  All formulas use the convention

    z = 1/w,  theta = w + beta,
    F^{-1}(y) / G_W(y) = exp(sum_{m>=1} h_m(theta) z^m).

Dependencies: Python 3.9+, mpmath, sympy, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

import mpmath as mp
import sympy as sp

# Matplotlib is imported only after the numerical work, so the coefficient
# engine remains usable in headless symbolic-only environments.


@dataclass(frozen=True)
class Constants:
    """Universal constants in the sharp endpoint expansion."""

    L: mp.mpf
    beta: mp.mpf
    Csharp: mp.mpf


def constants() -> Constants:
    """Return L=log 2, beta=1/L+1/2, and the sharp Fabius constant."""

    L = mp.log(2)
    gamma = mp.euler
    # mpmath.stieltjes(1) uses the conventional first Stieltjes constant
    # gamma_1 in zeta(s)=1/(s-1)+gamma-gamma_1(s-1)+...
    gamma1 = mp.stieltjes(1)
    Csharp = (
        (6 * gamma**2 + 12 * gamma1 - mp.pi**2) / (12 * L)
        - 7 * L / 12
        - mp.log(mp.pi) / 2
    )
    beta = 1 / L + mp.mpf("0.5")
    return Constants(L=L, beta=beta, Csharp=Csharp)


def wright_omega_real(x: mp.mpf) -> mp.mpf:
    """Evaluate the real Wright omega function: omega + log(omega) = x.

    The arguments in this project are large and positive.  Solving the defining
    equation avoids constructing exp(x), which would overflow in ordinary
    floating-point arithmetic.  Newton's method is monotone and very stable in
    this regime.
    """

    if x <= 1:
        # This branch is not normally reached by the endpoint tests, but the
        # Lambert-W definition provides a safe initial value.
        w = mp.lambertw(mp.e**x).real
    else:
        # Two terms of the large-x expansion make Newton converge immediately.
        lx = mp.log(x)
        w = x - lx + lx / x

    for _ in range(30):
        f = w + mp.log(w) - x
        step = f / (1 + 1 / w)
        w_next = w - step
        if abs(step) <= mp.eps * max(1, abs(w_next)) * 8:
            return +w_next
        w = w_next
    return +w


def exact_dyadic_moment_numbers(max_n: int) -> List[Fraction]:
    """Return d_0,...,d_max_n from the exact dyadic moment recurrence.

    The recurrence is

        d_0 = 1,
        d_m = [sum_{k<m} binom(m+1,k)d_k] / [(m+1)(2^m-1)].

    The corresponding exact Fabius value is

        F(2^{-n}) = d_n / (n! 2^{n(n-1)/2}).

    Fractions are used throughout; no rounding occurs.
    """

    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    d: List[Fraction] = [Fraction(1, 1)]
    for m in range(1, max_n + 1):
        numerator = sum(
            Fraction(math.comb(m + 1, k), 1) * d[k] for k in range(m)
        )
        denominator = (m + 1) * ((1 << m) - 1)
        d.append(numerator / denominator)
    return d


def exact_fabius_inverse_power_two(n: int, d: Sequence[Fraction] | None = None) -> Fraction:
    """Return the exact rational number F(2^{-n})."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    if d is None or len(d) <= n:
        d = exact_dyadic_moment_numbers(n)
    denominator = math.factorial(n) * (1 << (n * (n - 1) // 2))
    return d[n] / denominator


def fraction_log(value: Fraction) -> mp.mpf:
    """High-precision logarithm of a positive Fraction without float conversion."""

    if value <= 0:
        raise ValueError("value must be positive")
    return mp.log(mp.mpf(value.numerator)) - mp.log(mp.mpf(value.denominator))


def psi_derivatives(theta: mp.mpf, max_order: int, modes: int, L: mp.mpf) -> List[mp.mpf]:
    """Evaluate Psi(theta),...,Psi^(max_order)(theta) by Fourier summation.

    For k != 0,

        Psi_hat(k) = -Gamma(-chi_k) zeta(1-chi_k)/L,
        chi_k = 2*pi*i*k/L.

    Conjugate symmetry is used: only positive k are summed.  Gamma gives
    exponential mode decay, so six to nine positive modes are ample even for
    the derivatives used here.
    """

    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    if modes < 1:
        raise ValueError("modes must be positive")

    values = [mp.mpc(0) for _ in range(max_order + 1)]
    for k in range(1, modes + 1):
        chi = 2 * mp.pi * 1j * k / L
        coeff = -mp.gamma(-chi) * mp.zeta(1 - chi) / L
        phase = mp.e ** (2 * mp.pi * 1j * k * theta)
        frequency = 2 * mp.pi * 1j * k
        power = mp.mpc(1)
        for r in range(max_order + 1):
            values[r] += 2 * mp.re(coeff * power * phase)
            power *= frequency
    return [mp.mpf(mp.re(v)) for v in values]


def forward_a1_a2(P: Sequence[mp.mpf], L: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Return A_1, A_1', A_2 at the phase represented by P_r=Psi^(r)."""

    if len(P) < 5:
        raise ValueError("P must contain derivatives through Psi''''")
    p1, p2, p3, p4 = P[1], P[2], P[3], P[4]

    A1 = mp.mpf(1) / 24 + 1 / (2 * L) - (p2 + p1**2) / (2 * L**2)
    A1prime = -(p3 + 2 * p1 * p2) / (2 * L**2)

    A2 = (
        p1 / (24 * L)
        + (2 * p1 + 1) / (4 * L**2)
        - (p1**3 + 3 * p1**2 + 3 * p1 * p2 + 3 * p2 + p3) / (6 * L**3)
        + (4 * p1**2 * p2 + 4 * p1 * p3 + 2 * p2**2 + p4) / (8 * L**4)
    )
    return A1, A1prime, A2


@dataclass(frozen=True)
class Approximation:
    carrier: mp.mpf
    first: mp.mpf
    second: mp.mpf
    third: mp.mpf
    phase_scale: mp.mpf


def w_resummed_approximations(y: Fraction, modes: int, c: Constants) -> Approximation:
    """Compute the W-resummed carrier and corrections through h_3/w^3."""

    T = -fraction_log(y)
    H = T + c.Csharp + c.L * c.beta**2 / 2
    omega_argument = 4 * H + mp.log(2 * c.L)
    Omega = wright_omega_real(omega_argument)
    w = mp.sqrt(Omega / (2 * c.L))
    theta = w + c.beta

    P = psi_derivatives(theta, 4, modes=modes, L=c.L)
    p0, p1, p2 = P[0], P[1], P[2]
    A1, A1prime, A2 = forward_a1_a2(P, c.L)

    h1 = -p0
    h2 = c.beta / 2 - A1 + p0 * (1 - p1) / c.L
    h3 = (
        c.beta * A1
        - A2
        - c.beta**2 / 4
        + (
            -A1 * p1
            + A1
            - A1prime * p0
            + (p0**2 - 2 * c.beta * p0 + p0 + c.beta * p1 - c.beta) / 2
        )
        / c.L
        + p0 * (-p0 * p2 - 2 * p1**2 + 2 * p1) / (2 * c.L**2)
    )

    GW = theta * mp.e ** (-c.L * theta)
    first = GW * mp.e ** (h1 / w)
    second = GW * mp.e ** (h1 / w + h2 / w**2)
    third = GW * mp.e ** (h1 / w + h2 / w**2 + h3 / w**3)
    return Approximation(GW, first, second, third, w)


def rho_carrier_approximations(y: Fraction, modes: int, c: Constants) -> Approximation:
    """Compute the older square-root carrier and its first two corrections.

    This reproduces the normalization used in the pre-existing inverse frontier
    report and is included only as a numerical baseline.
    """

    T = -fraction_log(y)
    rho = mp.sqrt(2 * T / c.L)
    theta = rho + c.beta
    P = psi_derivatives(theta, 4, modes=modes, L=c.L)
    p0, p1 = P[0], P[1]
    A1, _, _ = forward_a1_a2(P, c.L)

    d1 = c.beta**2 / 2 + (c.Csharp + p0 - mp.log(rho) / 2) / c.L
    d2 = (p1 * d1 + A1 - c.beta / 2) / c.L
    h1 = c.beta - c.L * d1
    h2 = (1 - p1) * d1 - c.beta**2 / 2 - A1 + c.beta / 2

    G0 = rho * mp.e ** (-c.L * rho - c.L * c.beta)
    first = G0 * mp.e ** (h1 / rho)
    second = G0 * mp.e ** (h1 / rho + h2 / rho**2)
    # No third correction is needed for the comparison; repeat second so the
    # dataclass has a uniform shape.
    return Approximation(G0, first, second, second, rho)


def relative_error(approx: mp.mpf, exact: mp.mpf) -> mp.mpf:
    return approx / exact - 1


def symbolic_coefficients(order: int = 4) -> Mapping[str, List[sp.Expr]]:
    """Derive d_m, h_m, and g_m symbolically from the formal residual.

    The symbols A10, A11, ... stand for phase derivatives of A_j at theta:
    A10=A_1(theta), A11=A_1'(theta), A20=A_2(theta), etc.  P0, P1, ... stand for
    Psi(theta), Psi'(theta), ... .

    The calculation deliberately starts from the implicit equation rather than
    from the displayed formulas in the report.  It is therefore an independent
    algebraic consistency check.
    """

    if order < 1 or order > 6:
        raise ValueError("symbolic order must lie between 1 and 6")

    z, u, L, beta = sp.symbols("z u L beta", nonzero=True)
    P = sp.symbols(f"P0:{order + 2}")

    # A[j][r] denotes the r-th phase derivative of A_j(theta).
    A: Dict[int, Tuple[sp.Symbol, ...]] = {}
    for j in range(1, order):
        A[j] = sp.symbols(f"A{j}_0:{order + 1}")

    d_symbols = sp.symbols(f"d1:{order + 1}")
    D = sum(d_symbols[m - 1] * z**m for m in range(1, order + 1))

    def taylor(symbols: Sequence[sp.Symbol], arg: sp.Expr, max_degree: int) -> sp.Expr:
        return sum(symbols[r] * arg**r / sp.factorial(r) for r in range(min(len(symbols), max_degree + 1)))

    Psi = sum(P[r] * D**r / sp.factorial(r) for r in range(order + 1))
    one_plus = 1 + beta * z + z * D
    residual = sp.Rational(1, 2) * L * D**2 + sp.Rational(1, 2) * sp.log(one_plus) - Psi
    for j in range(1, order):
        residual -= taylor(A[j], D, order) * z**j * one_plus ** (-j)

    equation = L * D / z + residual
    truncated = sp.series(equation, z, 0, order).removeO().expand()

    solved: Dict[sp.Symbol, sp.Expr] = {}
    ds: List[sp.Expr] = []
    for m, symbol in enumerate(d_symbols):
        coefficient = sp.expand(truncated.subs(solved)).coeff(z, m)
        value = sp.factor(sp.solve(sp.Eq(coefficient, 0), symbol)[0])
        solved[symbol] = value
        ds.append(value)

    D_solved = sp.expand(D.subs(solved))
    H = sp.log(1 + z * D_solved / (1 + beta * z)) - L * D_solved
    H = sp.series(H, z, 0, order + 1).removeO().expand()
    hs = [sp.factor(H.coeff(z, m)) for m in range(1, order + 1)]

    expH = sp.series(sp.exp(H), z, 0, order + 1).removeO().expand()
    gs = [sp.factor(expH.coeff(z, m)) for m in range(1, order + 1)]
    return {"d": ds, "h": hs, "g": gs}


def write_symbolic_coefficients(path: Path, order: int) -> None:
    coeffs = symbolic_coefficients(order)
    with path.open("w", encoding="utf-8") as stream:
        stream.write("Symbolic W-resummed inverse coefficients\n")
        stream.write("========================================\n\n")
        stream.write("Notation: P0=Psi(theta), P1=Psi'(theta), ...; ")
        stream.write("A1_0=A_1(theta), A1_1=A_1'(theta), etc.\n\n")
        for family in ("d", "h", "g"):
            for index, expression in enumerate(coeffs[family], start=1):
                stream.write(f"{family}_{index} = {sp.sstr(expression)}\n\n")


def run_numerics(ns: Sequence[int], modes: int, output_dir: Path) -> List[Dict[str, str]]:
    c = constants()
    d = exact_dyadic_moment_numbers(max(ns))
    rows: List[Dict[str, str]] = []

    for n in ns:
        y = exact_fabius_inverse_power_two(n, d)
        exact_x = mp.power(2, -n)
        new = w_resummed_approximations(y, modes=modes, c=c)
        old = rho_carrier_approximations(y, modes=modes, c=c)

        new_errors = [
            relative_error(new.carrier, exact_x),
            relative_error(new.first, exact_x),
            relative_error(new.second, exact_x),
            relative_error(new.third, exact_x),
        ]
        old_errors = [
            relative_error(old.carrier, exact_x),
            relative_error(old.first, exact_x),
            relative_error(old.second, exact_x),
        ]

        rows.append(
            {
                "n": str(n),
                "log10_y": mp.nstr(mp.log10(mp.mpf(y.numerator) / mp.mpf(y.denominator)), 18),
                "w": mp.nstr(new.phase_scale, 18),
                "rho": mp.nstr(old.phase_scale, 18),
                "W_carrier_relerr": mp.nstr(new_errors[0], 18),
                "W_order1_relerr": mp.nstr(new_errors[1], 18),
                "W_order2_relerr": mp.nstr(new_errors[2], 18),
                "W_order3_relerr": mp.nstr(new_errors[3], 18),
                "rho_carrier_relerr": mp.nstr(old_errors[0], 18),
                "rho_order1_relerr": mp.nstr(old_errors[1], 18),
                "rho_order2_relerr": mp.nstr(old_errors[2], 18),
                "scaled_W2_w3": mp.nstr(new_errors[2] * new.phase_scale**3, 18),
                "scaled_W3_w4": mp.nstr(new_errors[3] * new.phase_scale**4, 18),
            }
        )

    csv_path = output_dir / "dyadic_inverse_comparison.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # Save a small exact-value ledger as a transparent cross-check.
    exact_path = output_dir / "exact_dyadic_values.txt"
    with exact_path.open("w", encoding="utf-8") as stream:
        for n in ns:
            y = exact_fabius_inverse_power_two(n, d)
            # Printing the full fraction becomes counterproductive at large n.
            # Preserve exact numerators/denominators for moderate depths and
            # record digit lengths plus a high-precision logarithm thereafter.
            if n <= 20:
                stream.write(f"n={n}: F(2^-n)={y.numerator}/{y.denominator}\n")
            else:
                numerator_digits = int(y.numerator.bit_length() * math.log10(2)) + 1
                denominator_digits = int(y.denominator.bit_length() * math.log10(2)) + 1
                stream.write(
                    f"n={n}: exact Fraction retained in memory; "
                    f"numerator_digits~{numerator_digits}, "
                    f"denominator_digits~{denominator_digits}, "
                    f"log10(F)={mp.nstr(fraction_log(y)/mp.log(10), 30)}\n"
                )

    return rows


def make_figures(rows: Sequence[Mapping[str, str]], output_dir: Path) -> None:
    import matplotlib.pyplot as plt

    ns = [int(row["n"]) for row in rows]

    def absolute(column: str) -> List[float]:
        return [abs(float(row[column])) for row in rows]

    fig = plt.figure(figsize=(8.0, 5.2))
    ax = fig.add_subplot(1, 1, 1)
    ax.semilogy(ns, absolute("rho_carrier_relerr"), marker="o", label="square-root carrier")
    ax.semilogy(ns, absolute("rho_order2_relerr"), marker="o", label="square-root through order 2")
    ax.semilogy(ns, absolute("W_carrier_relerr"), marker="s", label="Wright-omega carrier")
    ax.semilogy(ns, absolute("W_order2_relerr"), marker="s", label="Wright-omega through order 2")
    ax.semilogy(ns, absolute("W_order3_relerr"), marker="s", label="Wright-omega through order 3")
    ax.set_xlabel("dyadic depth n")
    ax.set_ylabel("absolute relative error")
    ax.set_title(r"Inverse Fabius endpoint approximations at $y=F(2^{-n})$")
    ax.grid(True, which="both", linewidth=0.4)
    ax.legend()
    fig.tight_layout()
    fig.savefig(output_dir / "carrier_comparison.png", dpi=180)
    fig.savefig(output_dir / "carrier_comparison.pdf")
    plt.close(fig)

    fig = plt.figure(figsize=(8.0, 5.0))
    ax = fig.add_subplot(1, 1, 1)
    ax.plot(ns, [float(row["scaled_W2_w3"]) for row in rows], marker="o", label=r"$w^3$ times order-2 error")
    ax.plot(ns, [float(row["scaled_W3_w4"]) for row in rows], marker="s", label=r"$w^4$ times order-3 error")
    ax.set_xlabel("dyadic depth n")
    ax.set_ylabel("scaled relative error")
    ax.set_title("Stabilization of the first omitted W-resummed coefficients")
    ax.grid(True, linewidth=0.4)
    ax.legend()
    fig.tight_layout()
    fig.savefig(output_dir / "scaled_residuals.png", dpi=180)
    fig.savefig(output_dir / "scaled_residuals.pdf")
    plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "data",
        help="directory for CSV, text, and figure outputs",
    )
    parser.add_argument("--dps", type=int, default=100, help="mpmath decimal precision")
    parser.add_argument("--modes", type=int, default=9, help="positive Fourier modes for Psi")
    parser.add_argument(
        "--symbolic-order",
        type=int,
        default=3,
        help="derive formal d/h/g coefficients through this order (1..6; orders above 3 can be slow)",
    )
    parser.add_argument(
        "--depths",
        type=int,
        nargs="*",
        default=[5, 10, 20, 40, 80, 100, 160],
        help="dyadic depths n used in exact endpoint tests",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if any(n < 1 for n in args.depths):
        raise SystemExit("all dyadic depths must be positive")
    mp.mp.dps = args.dps
    args.output_dir.mkdir(parents=True, exist_ok=True)

    rows = run_numerics(args.depths, modes=args.modes, output_dir=args.output_dir)
    write_symbolic_coefficients(
        args.output_dir / "symbolic_inverse_coefficients.txt",
        order=args.symbolic_order,
    )
    make_figures(rows, output_dir=args.output_dir)

    c = constants()
    print(f"L       = {mp.nstr(c.L, 30)}")
    print(f"beta    = {mp.nstr(c.beta, 30)}")
    print(f"Csharp  = {mp.nstr(c.Csharp, 30)}")
    print(f"Wrote {len(rows)} numerical rows to {args.output_dir}")


if __name__ == "__main__":
    main()
