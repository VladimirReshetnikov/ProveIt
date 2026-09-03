#!/usr/bin/env python3
r"""
Reproducibility calculations for

    Closed all-orders endpoint asymptotics for the inverse Fabius function.

The script has three independent purposes.

1. Exact dyadic endpoint tests.
   For n >= 0 it computes F(2^{-n}) by the exact rational recurrence

       a_0 = 1,
       a_n = (2^n-1)^{-1} sum_{k=0}^{n-1} a_k/(n-k+1)!,
       F(2^{-n}) = 2^{-n(n-1)/2} a_n.

   Consequently G(F(2^{-n})) = 2^{-n} is known without numerical root
   finding.  These exact points test the endpoint inverse expansion.

2. High-precision Gamma-zeta evaluation.
   The one-periodic fluctuation Psi and its derivatives are evaluated from

       Psi_hat(k) = -Gamma(-chi_k) zeta(1-chi_k)/log(2),
       chi_k = 2*pi*i*k/log(2),       k != 0.

   Exponential Gamma decay makes a small number of modes sufficient.

3. Symbolic checks of the new diagonal Lagrange-Buermann formula.
   The formal equation D = z Phi(z,D) is solved both by the triangular
   recursion and by

       d_n = sum_{k=1}^n (1/k) [z^{n-k} w^{k-1}] Phi(z,w)^k.

   The two answers are compared exactly through third order, and the
   explicit d_1,d_2,d_3 and h_1,h_2,h_3 formulas are checked.

Outputs (in --output-dir):
  endpoint_errors.csv
  endpoint_error_plot.pdf
  endpoint_error_plot.png
  constants.txt
  symbolic_checks.txt

Dependencies: Python 3.10+, mpmath, sympy, matplotlib.
No network access is used.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import sympy as sp


@dataclass(frozen=True)
class EndpointConstants:
    """Numerical constants in the exact Lambert phase normalization."""

    L: mp.mpf
    beta: mp.mpf
    Csharp: mp.mpf
    kappa0: mp.mpf


def endpoint_constants() -> EndpointConstants:
    """Return L, beta, C_sharp, and kappa_0 at current mp precision."""
    L = mp.log(2)
    beta = 1 / L + mp.mpf("0.5")
    gamma1 = mp.stieltjes(1)
    Csharp = (
        (6 * mp.euler**2 + 12 * gamma1 - mp.pi**2) / (12 * L)
        - 7 * L / 12
        - mp.log(mp.pi) / 2
    )
    kappa0 = beta - L * beta**2 / 2 - Csharp
    return EndpointConstants(L=L, beta=beta, Csharp=Csharp, kappa0=kappa0)


def psi_hat(k: int, c: EndpointConstants) -> mp.mpc:
    """Fourier coefficient of the endpoint fluctuation Psi for k != 0."""
    if k == 0:
        return mp.mpc(0)
    chi = 2 * mp.pi * 1j * k / c.L
    return -mp.gamma(-chi) * mp.zeta(1 - chi) / c.L


def psi_derivative(u: mp.mpf, order: int, modes: int, c: EndpointConstants) -> mp.mpf:
    r"""Evaluate Psi^{(order)}(u) using conjugate positive/negative modes.

    Because Psi_hat(-k) is the complex conjugate of Psi_hat(k), the real
    Fourier series can be summed as twice the real part of the k>0 terms.
    """
    total = mp.mpc(0)
    for k in range(1, modes + 1):
        total += (
            (2 * mp.pi * 1j * k) ** order
            * psi_hat(k, c)
            * mp.e ** (2 * mp.pi * 1j * k * u)
        )
    return mp.mpf(2 * mp.re(total))


def dyadic_moment_sequence(max_n: int) -> list[Fraction]:
    """Return exact a_0,...,a_max_n in the dyadic moment recurrence."""
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    a: list[Fraction] = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        numerator = sum(a[k] / math.factorial(n - k + 1) for k in range(n))
        a.append(numerator / (2**n - 1))
    return a


def dyadic_f_value(n: int, moments: Sequence[Fraction]) -> Fraction:
    """Return the exact rational value F(2^{-n})."""
    if not (0 <= n < len(moments)):
        raise ValueError("moments must contain a_n")
    return moments[n] / 2 ** (n * (n - 1) // 2)


def mp_log_fraction(value: Fraction) -> mp.mpf:
    """High-precision logarithm of a positive Fraction without underflow."""
    if value <= 0:
        raise ValueError("value must be positive")
    return mp.log(value.numerator) - mp.log(value.denominator)


@dataclass(frozen=True)
class InverseCoefficients:
    """Endpoint variables and the first three phase/log coefficients."""

    rho: mp.mpf
    ell: mp.mpf
    theta: mp.mpf
    G0: mp.mpf
    d: tuple[mp.mpf, mp.mpf, mp.mpf]
    h: tuple[mp.mpf, mp.mpf, mp.mpf]
    psi_jets: tuple[mp.mpf, ...]
    A1: mp.mpf
    A1prime: mp.mpf
    A2: mp.mpf


def inverse_coefficients_from_log_y(
    log_y: mp.mpf, modes: int, c: EndpointConstants
) -> InverseCoefficients:
    r"""Compute d_1,d_2,d_3 and h_1,h_2,h_3 for y=exp(log_y).

    The forward coefficients used are

      A1 = 1/24 + 1/(2L) - (Psi'' + (Psi')^2)/(2L^2),

    and the explicit A2 differential polynomial recorded in the repository.
    The third inverse coefficient is the new compact consequence

      d3 = -(1/L) [ L d1^2/2 + d1/2 - beta^2/4
                    - Psi' d2 - Psi'' d1^2/2
                    - A1' d1 + beta A1 - A2 ].
    """
    if log_y >= 0:
        raise ValueError("endpoint formula expects 0 < y < 1")

    T = -log_y
    rho = mp.sqrt(2 * T / c.L)
    ell = mp.log(rho)
    theta = rho + c.beta
    jets = tuple(psi_derivative(theta, r, modes, c) for r in range(5))
    P0, P1, P2, P3, P4 = jets

    A1 = mp.mpf(1) / 24 + 1 / (2 * c.L) - (P2 + P1**2) / (2 * c.L**2)
    A1prime = -(P3 + 2 * P1 * P2) / (2 * c.L**2)
    A2 = (
        P1 / (24 * c.L)
        + (2 * P1 + 1) / (4 * c.L**2)
        - (P1**3 + 3 * P1**2 + 3 * P1 * P2 + 3 * P2 + P3) / (6 * c.L**3)
        + (4 * P1**2 * P2 + 4 * P1 * P3 + 2 * P2**2 + P4) / (8 * c.L**4)
    )

    d1 = c.beta**2 / 2 + (c.Csharp + P0 - ell / 2) / c.L
    d2 = (P1 * d1 + A1 - c.beta / 2) / c.L
    d3 = -(
        c.L * d1**2 / 2
        + d1 / 2
        - c.beta**2 / 4
        - P1 * d2
        - P2 * d1**2 / 2
        - A1prime * d1
        + c.beta * A1
        - A2
    ) / c.L

    # log(G/G0) = log(1+beta z+zD)-LD, z=1/rho.
    h1 = c.beta - c.L * d1
    h2 = d1 - c.beta**2 / 2 - c.L * d2
    h3 = d2 - c.beta * d1 + c.beta**3 / 3 - c.L * d3

    G0 = rho * mp.e ** (-c.L * rho - c.L * c.beta)
    return InverseCoefficients(
        rho=rho,
        ell=ell,
        theta=theta,
        G0=G0,
        d=(d1, d2, d3),
        h=(h1, h2, h3),
        psi_jets=jets,
        A1=A1,
        A1prime=A1prime,
        A2=A2,
    )


def inverse_approximation(coeffs: InverseCoefficients, order: int) -> mp.mpf:
    """Return G0*exp(sum_{j=1}^order h_j/rho^j), for 0 <= order <= 3."""
    if not 0 <= order <= 3:
        raise ValueError("this numerical demonstrator implements orders 0 through 3")
    exponent = mp.fsum(coeffs.h[j] / coeffs.rho ** (j + 1) for j in range(order))
    return coeffs.G0 * mp.e**exponent


def coefficient(expr: sp.Expr, var: sp.Symbol, degree: int) -> sp.Expr:
    """Coefficient extraction after a finite Taylor expansion."""
    return sp.expand(expr).coeff(var, degree)


def truncate(expr: sp.Expr, var: sp.Symbol, order: int) -> sp.Expr:
    """Truncate at powers < order in var."""
    return sp.series(expr, var, 0, order).removeO().expand()


def diagonal_phase_coefficients(
    phi: sp.Expr, z: sp.Symbol, w: sp.Symbol, max_order: int
) -> list[sp.Expr]:
    r"""Apply the diagonal Lagrange-Buermann formula to D=z Phi(z,D).

    This routine is completely general: ``phi`` may have coefficients in any
    commutative SymPy expression ring.  For a high order calculation, truncate
    phi in z and w before calling this function.
    """
    answer: list[sp.Expr] = []
    for n in range(1, max_order + 1):
        dn = sp.Integer(0)
        for k in range(1, n + 1):
            # ``phi`` is supplied as a polynomial truncated to the needed
            # z-order.  Expanding the positive integer power directly avoids
            # a SymPy series-normalization artifact that can leave removable
            # rational factors in the coefficient ring.
            phik = sp.expand(phi**k)
            term_z = coefficient(phik, z, n - k)
            dn += coefficient(sp.expand(term_z), w, k - 1) / k
        answer.append(sp.factor(dn))
    return answer


def triangular_phase_coefficients(
    phi: sp.Expr, z: sp.Symbol, w: sp.Symbol, max_order: int
) -> list[sp.Expr]:
    """Solve D=z Phi(z,D) by the repository's triangular recursion."""
    D = sp.Integer(0)
    answer: list[sp.Expr] = []
    for n in range(1, max_order + 1):
        rhs = truncate(z * phi.subs(w, D), z, n + 1)
        dn = sp.factor(coefficient(rhs, z, n))
        answer.append(dn)
        D += dn * z**n
    return answer


def symbolic_checks() -> str:
    """Run exact checks through third order and return a human-readable log."""
    z, w = sp.symbols("z w")
    L, beta, C, ell = sp.symbols("L beta C ell", nonzero=True)
    P0, P1, P2, P3, P4 = sp.symbols("P0 P1 P2 P3 P4")
    A10, A11, A20 = sp.symbols("A10 A11 A20")

    # Only the Taylor jets required through d3 are retained.
    psi = P0 + P1 * w + P2 * w**2 / 2 + P3 * w**3 / 6 + P4 * w**4 / 24
    A1w = A10 + A11 * w
    A2w = A20
    phi = (
        beta**2 / 2
        - w**2 / 2
        - ell / (2 * L)
        - sp.log(1 + beta * z + z * w) / (2 * L)
        + (C + psi) / L
        + A1w * z * (1 + beta * z + z * w) ** (-1) / L
        + A2w * z**2 * (1 + beta * z + z * w) ** (-2) / L
    )
    phi = truncate(phi, z, 3)

    diag = diagonal_phase_coefficients(phi, z, w, 3)
    tri = triangular_phase_coefficients(phi, z, w, 3)

    d1 = beta**2 / 2 + (C + P0 - ell / 2) / L
    d2 = (P1 * d1 + A10 - beta / 2) / L
    d3 = -(
        L * d1**2 / 2
        + d1 / 2
        - beta**2 / 4
        - P1 * d2
        - P2 * d1**2 / 2
        - A11 * d1
        + beta * A10
        - A20
    ) / L
    explicit = [d1, d2, d3]

    lines = ["Exact symbolic checks", "====================="]
    for n in range(3):
        delta_dt = sp.simplify(diag[n] - tri[n])
        delta_de = sp.simplify(diag[n] - explicit[n])
        lines.append(f"order {n+1}: diagonal - triangular = {delta_dt}")
        lines.append(f"order {n+1}: diagonal - explicit   = {delta_de}")
        if delta_dt != 0 or delta_de != 0:
            raise AssertionError(f"symbolic phase check failed at order {n+1}")

    D = sum(explicit[n - 1] * z**n for n in range(1, 4))
    H = truncate(sp.log(1 + beta * z + z * D) - L * D, z, 4)
    h1 = beta - L * d1
    h2 = d1 - beta**2 / 2 - L * d2
    h3 = d2 - beta * d1 + beta**3 / 3 - L * d3
    for n, hn in enumerate((h1, h2, h3), start=1):
        delta = sp.simplify(coefficient(H, z, n) - hn)
        lines.append(f"h_{n} extraction check = {delta}")
        if delta != 0:
            raise AssertionError(f"symbolic h check failed at order {n}")

    # Degree and leading-log checks at the orders represented here.
    expected_d_leads = [
        -sp.Rational(1, 2) / L,
        -P1 / (2 * L**2),
        (P2 - L) / (8 * L**3),
    ]
    expected_h_leads = [
        sp.Rational(1, 2),
        (P1 - 1) / (2 * L),
        (L - P2) / (8 * L**2),
    ]
    for n, expr in enumerate(explicit, start=1):
        poly = sp.Poly(sp.expand(expr), ell)
        lead = poly.coeff_monomial(ell ** poly.degree())
        lines.append(f"d_{n}: degree_ell={poly.degree()}, leading coefficient={lead}")
        if sp.simplify(lead - expected_d_leads[n - 1]) != 0:
            raise AssertionError(f"leading-log d_{n} check failed")
    for n, expr in enumerate((h1, h2, h3), start=1):
        poly = sp.Poly(sp.expand(expr), ell)
        lead = poly.coeff_monomial(ell ** poly.degree())
        lines.append(f"h_{n}: degree_ell={poly.degree()}, leading coefficient={lead}")
        if sp.simplify(lead - expected_h_leads[n - 1]) != 0:
            raise AssertionError(f"leading-log h_{n} check failed")

    # Bell conversion through order three, with an inexpensive leading-log check.
    g1 = h1
    g2 = h2 + h1**2 / 2
    g3 = h3 + h1 * h2 + h1**3 / 6
    for n, gn in enumerate((g1, g2, g3), start=1):
        poly = sp.Poly(sp.expand(gn), ell)
        top = poly.coeff_monomial(ell**n)
        target = sp.Rational(1, 2**n * math.factorial(n))
        lines.append(f"g_{n}: [ell^{n}]g_{n}={top} (target {target})")
        if sp.simplify(top - target) != 0:
            raise AssertionError(f"universal top-log g_{n} check failed")

    # The n=3 highest periodic derivative comes only from -A2 in h3/g3.
    # Insert the known top term A2 = P4/(8 L^4)+lower jets.
    topjet_h3 = sp.diff(h3.subs(A20, P4 / (8 * L**4)), P4)
    lines.append(f"[P4] h_3 = {sp.simplify(topjet_h3)} (target -1/(8 L^4))")
    if sp.simplify(topjet_h3 + 1 / (8 * L**4)) != 0:
        raise AssertionError("top-jet h3 check failed")

    lines.append("All exact symbolic checks passed.")
    return "\n".join(lines) + "\n"


def write_endpoint_table(
    output_dir: Path,
    depths: Iterable[int],
    modes: int,
    precision: int,
) -> list[dict[str, str]]:
    """Compute exact dyadic tests, write CSV, and return formatted rows."""
    mp.mp.dps = precision
    c = endpoint_constants()
    depths = list(depths)
    moments = dyadic_moment_sequence(max(depths))
    rows: list[dict[str, str]] = []

    for n in depths:
        y_exact = dyadic_f_value(n, moments)
        coeffs = inverse_coefficients_from_log_y(mp_log_fraction(y_exact), modes, c)
        true_inverse = mp.power(2, -n)
        errors = [inverse_approximation(coeffs, j) / true_inverse - 1 for j in range(4)]
        row = {
            "n": str(n),
            "rho": mp.nstr(coeffs.rho, 18),
            "theta_mod_1": mp.nstr(mp.frac(coeffs.theta), 18),
            "relative_error_order_0": mp.nstr(errors[0], 18),
            "relative_error_order_1": mp.nstr(errors[1], 18),
            "relative_error_order_2": mp.nstr(errors[2], 18),
            "relative_error_order_3": mp.nstr(errors[3], 18),
        }
        rows.append(row)

    csv_path = output_dir / "endpoint_errors.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def make_error_plot(output_dir: Path, rows: Sequence[dict[str, str]]) -> None:
    """Plot absolute relative errors for the four truncation orders."""
    import matplotlib.pyplot as plt

    rho = [float(row["rho"]) for row in rows]
    plt.figure(figsize=(7.2, 4.8))
    for order in range(4):
        err = [abs(float(row[f"relative_error_order_{order}"])) for row in rows]
        plt.semilogy(rho, err, marker="o", label=f"through $h_{order}$" if order else "$G_0$ only")
    plt.xlabel(r"$\rho=\sqrt{2\log(1/y)/\log 2}$")
    plt.ylabel("absolute relative error")
    plt.title(r"Inverse Fabius endpoint expansion at $y_n=F(2^{-n})$")
    plt.grid(True, which="both", linewidth=0.4, alpha=0.5)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "endpoint_error_plot.pdf")
    plt.savefig(output_dir / "endpoint_error_plot.png", dpi=220)
    plt.close()


def write_constants(output_dir: Path, modes: int, precision: int) -> None:
    """Record constants and the leading Fourier mode."""
    mp.mp.dps = precision
    c = endpoint_constants()
    c1 = psi_hat(1, c)
    text = (
        f"precision = {precision} decimal digits\n"
        f"Fourier modes used in tables = {modes}\n"
        f"L = {mp.nstr(c.L, 80)}\n"
        f"beta = {mp.nstr(c.beta, 80)}\n"
        f"Csharp = {mp.nstr(c.Csharp, 80)}\n"
        f"kappa0 = {mp.nstr(c.kappa0, 80)}\n"
        f"Psi_hat(1) = {mp.nstr(c1, 80)}\n"
        f"abs(Psi_hat(1)) = {mp.nstr(abs(c1), 80)}\n"
        f"arg(Psi_hat(1)) = {mp.nstr(mp.arg(c1), 80)}\n"
    )
    (output_dir / "constants.txt").write_text(text, encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results"),
        help="directory for CSV, figures, and verification logs",
    )
    parser.add_argument("--precision", type=int, default=100, help="mpmath decimal precision")
    parser.add_argument("--modes", type=int, default=12, help="positive Fourier modes")
    parser.add_argument(
        "--depths",
        type=int,
        nargs="*",
        default=[5, 10, 20, 40, 80, 120, 160],
        help="dyadic depths n for exact tests",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = write_endpoint_table(args.output_dir, args.depths, args.modes, args.precision)
    make_error_plot(args.output_dir, rows)
    write_constants(args.output_dir, args.modes, args.precision)
    checks = symbolic_checks()
    (args.output_dir / "symbolic_checks.txt").write_text(checks, encoding="utf-8")

    print(f"Wrote reproducibility outputs to {args.output_dir.resolve()}")
    for row in rows:
        print(
            f"n={row['n']:>3} rho={row['rho'][:12]:>12} "
            f"err0={row['relative_error_order_0'][:12]:>12} "
            f"err1={row['relative_error_order_1'][:12]:>12} "
            f"err2={row['relative_error_order_2'][:12]:>12} "
            f"err3={row['relative_error_order_3'][:12]:>12}"
        )
    print(checks.splitlines()[-1])


if __name__ == "__main__":
    main()
