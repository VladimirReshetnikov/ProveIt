#!/usr/bin/env python3
"""Numerical experiments for *The Lambert W Function: A Real-Variable Guide*.

This script reproduces every numerical figure and the small value table used in
(or supplied with) the article.  It deliberately uses mpmath's high-precision
Lambert W implementation only as a reference value.  All approximations being
studied are implemented explicitly below.

Run from the article directory with

    python3 numerical_experiments.py

or choose a different output directory with

    python3 numerical_experiments.py --output-dir figures

Dependencies: mpmath, numpy, matplotlib.  No Internet access is used.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import matplotlib

# A non-interactive backend makes the script reproducible on servers.
matplotlib.use("Agg")
# Embed scalable TrueType glyphs in the vector-PDF figures rather than
# Type 3 bitmap-like fonts.  This improves searchability and portability.
matplotlib.rcParams.update({"pdf.fonttype": 42, "ps.fonttype": 42})
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


# Fifty decimal digits are much more than the plotted double-precision data
# require.  They prevent the reference values from dominating approximation
# errors near the branch point x=-1/e.
mp.mp.dps = 80


def W0(x: float | mp.mpf) -> mp.mpf:
    """Return the real principal branch W_0(x)."""
    z = mp.lambertw(mp.mpf(x), 0)
    return mp.re(z)


def Wm1(x: float | mp.mpf) -> mp.mpf:
    """Return the real nonprincipal branch W_{-1}(x), -1/e <= x < 0."""
    z = mp.lambertw(mp.mpf(x), -1)
    return mp.re(z)


def branch_point_series(x: float | mp.mpf, branch: int = 0, order: int = 6) -> mp.mpf:
    """Puiseux approximation at x=-1/e through the requested order.

    We use p = +/-sqrt(2(1+e*x)); the plus sign selects W_0 and the minus sign
    selects W_{-1}.  The coefficients are exact rational numbers transcribed
    from the coefficient recurrence proved in the article.
    """
    if branch not in (0, -1):
        raise ValueError("branch must be 0 or -1")
    if order < 1 or order > 9:
        raise ValueError("implemented orders are 1 through 9")

    coeffs = [
        mp.mpf(1),
        -mp.mpf(1) / 3,
        mp.mpf(11) / 72,
        -mp.mpf(43) / 540,
        mp.mpf(769) / 17280,
        -mp.mpf(221) / 8505,
        mp.mpf(680863) / 43545600,
        -mp.mpf(1963) / 204120,
        mp.mpf(226287557) / 37623398400,
    ]
    p = mp.sqrt(2 * (1 + mp.e * mp.mpf(x)))
    if branch == -1:
        p = -p
    value = mp.mpf(-1)
    for n in range(1, order + 1):
        value += coeffs[n - 1] * p**n
    return value


def asymptotic_real(x: float | mp.mpf, branch: int = 0, order: int = 4) -> mp.mpf:
    """Classical logarithmic asymptotic expansion for W_0 or W_{-1}.

    For W_0, x must be greater than 1 and L1=log(x).  For W_{-1}, x must be
    negative and close to zero, L1=log(-x)<0.  In both cases L2=log(|L1|), and
    the same algebraic formula applies.  `order` counts inverse powers of L1.
    """
    if branch == 0:
        if x <= 1:
            raise ValueError("W_0 asymptotic form is used here only for x>1")
        L1 = mp.log(x)
    elif branch == -1:
        if not (-1 / mp.e < x < 0):
            raise ValueError("W_{-1} requires -1/e < x < 0")
        L1 = mp.log(-x)
    else:
        raise ValueError("branch must be 0 or -1")

    L2 = mp.log(abs(L1))
    value = L1 - L2
    if order >= 1:
        value += L2 / L1
    if order >= 2:
        value += L2 * (-2 + L2) / (2 * L1**2)
    if order >= 3:
        value += L2 * (6 - 9 * L2 + 2 * L2**2) / (6 * L1**3)
    if order >= 4:
        value += L2 * (-12 + 36 * L2 - 22 * L2**2 + 3 * L2**3) / (12 * L1**4)
    if order > 4:
        raise ValueError("this plotting implementation supplies orders 0 through 4")
    return value


def pade_11(x: float | mp.mpf) -> mp.mpf:
    """The [1/1] Pade approximant at the origin."""
    x = mp.mpf(x)
    return x / (1 + x)


def pade_22(x: float | mp.mpf) -> mp.mpf:
    """The [2/2] Pade approximant at the origin."""
    x = mp.mpf(x)
    return 2 * x * (4 * x + 3) / (5 * x**2 + 14 * x + 6)


def pade_33(x: float | mp.mpf) -> mp.mpf:
    """The [3/3] Pade approximant at the origin."""
    x = mp.mpf(x)
    num = 3 * x * (451 * x**2 + 912 * x + 340)
    den = 665 * x**3 + 3579 * x**2 + 3756 * x + 1020
    return num / den


def chatzigeorgiou_bounds(u: float | mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    """Return lower and upper bounds for W_{-1}(-exp(-1-u))."""
    u = mp.mpf(u)
    root = mp.sqrt(2 * u)
    lower = -1 - root - u
    upper = -1 - root - mp.mpf(2) * u / 3
    return lower, upper


def logarithmic_newton(x: float | mp.mpf, branch: int, iterations: int = 8) -> List[mp.mpf]:
    """Compute a branch-safe logarithmic Newton sequence.

    Newton is applied to w+log|w|=log|x|.  The starts are elementary bounds:
      * x>0: x/(1+x), except that the first two logarithmic asymptotic terms
        are used for x>=e;
      * -1/e<x<0, W_0: x;
      * W_{-1}: the lower Chatzigeorgiou bound.
    The article proves monotone convergence from these starts.
    """
    x = mp.mpf(x)
    if branch == 0:
        if x > 0:
            w = mp.log(x) - mp.log(mp.log(x)) if x >= mp.e else x / (1 + x)
        elif -1 / mp.e < x < 0:
            w = x
        elif x == 0:
            return [mp.mpf(0)]
        elif x == -1 / mp.e:
            return [mp.mpf(-1)]
        else:
            raise ValueError("x is outside the real domain of W_0")
    elif branch == -1:
        if not (-1 / mp.e < x < 0):
            raise ValueError("W_{-1} requires -1/e < x < 0")
        u = -1 - mp.log(-x)
        w = -1 - mp.sqrt(2 * u) - u
    else:
        raise ValueError("branch must be 0 or -1")

    values = [w]
    for _ in range(iterations):
        w = (w / (1 + w)) * (1 + mp.log(abs(x / w)))
        values.append(w)
    return values


def _as_float(values: Iterable[mp.mpf]) -> np.ndarray:
    """Convert finite high-precision numbers to a NumPy float array."""
    return np.asarray([float(v) for v in values], dtype=float)


def make_real_branch_figure(out_dir: Path) -> None:
    """Plot both real branches and mark the common branch point."""
    xmin = -1 / math.e
    x0 = np.linspace(xmin + 1e-10, 8.0, 900)
    # A geometric grid resolves the logarithmic divergence of W_{-1} at zero.
    delta = np.geomspace(1e-8, 1 / math.e - 1e-9, 650)
    xm = -delta[::-1]

    y0 = _as_float(W0(x) for x in x0)
    ym = _as_float(Wm1(x) for x in xm)

    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    ax.plot(x0, y0, label=r"$W_0(x)$")
    ax.plot(xm, ym, label=r"$W_{-1}(x)$")
    ax.scatter([xmin], [-1], zorder=4)
    ax.axhline(0, linewidth=0.7)
    ax.axvline(0, linewidth=0.7)
    ax.set_xlim(xmin - 0.04, 8)
    ax.set_ylim(-8, 2.2)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$W(x)$")
    ax.set_title("The two real branches of the Lambert W function")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "real_branches.pdf")
    plt.close(fig)


def make_branch_point_error_figures(out_dir: Path) -> None:
    """Show convergence of the Puiseux expansion on each real branch."""
    deltas = np.geomspace(1e-14, 0.45, 350)
    xs = (deltas - 1) / math.e
    for branch, name, exact_fun in [(0, "W0", W0), (-1, "Wm1", Wm1)]:
        exact = [exact_fun(x) for x in xs]
        fig, ax = plt.subplots(figsize=(7.2, 4.8))
        for order in (1, 2, 4, 6):
            errors = [abs(branch_point_series(x, branch, order) - y) for x, y in zip(xs, exact)]
            ax.loglog(deltas, _as_float(errors), label=f"through order {order}")
        ax.set_xlabel(r"$1+ex$")
        ax.set_ylabel("absolute error")
        branch_label = r"$W_0$" if branch == 0 else r"$W_{-1}$"
        ax.set_title(f"Puiseux approximation error for {branch_label}")
        ax.legend()
        ax.grid(True, which="both", alpha=0.25)
        fig.tight_layout()
        fig.savefig(out_dir / f"branch_point_error_{name}.pdf")
        plt.close(fig)


def make_asymptotic_error_figures(out_dir: Path) -> None:
    """Plot truncation errors for the logarithmic asymptotic expansion."""
    # Parameterizing by L1 prevents overflow while covering enormous arguments.
    L1_values = np.linspace(2.0, 55.0, 350)
    x0_values = [mp.e ** mp.mpf(v) for v in L1_values]
    exact0 = [W0(x) for x in x0_values]
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    for order in (0, 1, 2, 3, 4):
        errors = [abs(asymptotic_real(x, 0, order) - y) for x, y in zip(x0_values, exact0)]
        ax.semilogy(L1_values, _as_float(errors), label=f"order {order}")
    ax.set_xlabel(r"$L_1=\log x$")
    ax.set_ylabel("absolute error")
    ax.set_title(r"Logarithmic asymptotics for $W_0(x)$")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "asymptotic_error_W0.pdf")
    plt.close(fig)

    eta_values = np.linspace(2.0, 55.0, 350)
    xm_values = [-mp.e ** (-mp.mpf(v)) for v in eta_values]
    exactm = [Wm1(x) for x in xm_values]
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    for order in (0, 1, 2, 3, 4):
        errors = [abs(asymptotic_real(x, -1, order) - y) for x, y in zip(xm_values, exactm)]
        ax.semilogy(eta_values, _as_float(errors), label=f"order {order}")
    ax.set_xlabel(r"$\eta=\log(1/(-x))$")
    ax.set_ylabel("absolute error")
    ax.set_title(r"Logarithmic asymptotics for $W_{-1}(x)$")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "asymptotic_error_Wm1.pdf")
    plt.close(fig)


def make_bound_figure(out_dir: Path) -> None:
    """Plot the elementary two-sided W_{-1} bounds proved in the article."""
    u_values = np.geomspace(1e-7, 30.0, 500)
    exact = [Wm1(-mp.e ** (-1 - mp.mpf(u))) for u in u_values]
    lower, upper = zip(*(chatzigeorgiou_bounds(u) for u in u_values))

    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    ax.semilogx(u_values, _as_float(exact), label=r"$W_{-1}(-e^{-1-u})$")
    ax.semilogx(u_values, _as_float(lower), label="lower bound")
    ax.semilogx(u_values, _as_float(upper), label="upper bound")
    ax.set_xlabel(r"$u$")
    ax.set_ylabel("value")
    ax.set_title(r"Elementary bounds for the nonprincipal real branch")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "Wm1_bounds.pdf")
    plt.close(fig)


def make_newton_figure(out_dir: Path) -> None:
    """Compare monotone logarithmic Newton convergence in three regimes."""
    cases: Sequence[Tuple[float, int, str]] = [
        (10.0, 0, r"$W_0(10)$"),
        (-0.30, 0, r"$W_0(-0.30)$"),
        (-0.10, -1, r"$W_{-1}(-0.10)$"),
    ]
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    for x, branch, label in cases:
        values = logarithmic_newton(x, branch, iterations=8)
        root = W0(x) if branch == 0 else Wm1(x)
        errors = [abs(w - root) for w in values]
        # Matplotlib cannot display exact zero on a log scale.  Clip only for
        # plotting; the underlying high-precision computation is unchanged.
        errors_float = np.maximum(_as_float(errors), 1e-80)
        ax.semilogy(range(len(values)), errors_float, marker="o", label=label)
    ax.set_xlabel("iteration number")
    ax.set_ylabel("absolute error")
    ax.set_title("Branch-safe logarithmic Newton iteration")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "logarithmic_newton_convergence.pdf")
    plt.close(fig)


def make_pade_figure(out_dir: Path) -> None:
    """Compare three Pade approximants to the Maclaurin branch W_0."""
    xs = np.linspace(-0.32, 1.5, 500)
    exact = [W0(x) for x in xs]
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    for function, label in [(pade_11, "[1/1]"), (pade_22, "[2/2]"), (pade_33, "[3/3]")]:
        errors = [abs(function(x) - y) for x, y in zip(xs, exact)]
        ax.semilogy(xs, np.maximum(_as_float(errors), 1e-18), label=label)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("absolute error")
    ax.set_title(r"Pade approximants to $W_0$ about the origin")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "pade_errors.pdf")
    plt.close(fig)


def write_value_table(article_dir: Path) -> None:
    """Write a compact plain-text table of reference values and residuals."""
    rows: Sequence[Tuple[str, mp.mpf, int]] = [
        ("-1/e", -1 / mp.e, 0),
        ("-0.35", mp.mpf("-0.35"), 0),
        ("-0.35", mp.mpf("-0.35"), -1),
        ("-0.10", mp.mpf("-0.10"), 0),
        ("-0.10", mp.mpf("-0.10"), -1),
        ("-0.001", mp.mpf("-0.001"), -1),
        ("0", mp.mpf("0"), 0),
        ("0.1", mp.mpf("0.1"), 0),
        ("1", mp.mpf("1"), 0),
        ("e", mp.e, 0),
        ("10", mp.mpf("10"), 0),
        ("10^6", mp.mpf(10) ** 6, 0),
    ]
    lines = [
        "Reference values generated with mpmath at 80 decimal digits",
        "x              branch        W_k(x)                    |W exp(W)-x|",
        "-" * 79,
    ]
    for label, x, branch in rows:
        if x == -1 / mp.e:
            w = mp.mpf(-1)
        else:
            w = W0(x) if branch == 0 else Wm1(x)
        residual = abs(w * mp.e**w - x)
        lines.append(f"{label:12s} {branch:>4d}   {mp.nstr(w, 20):>24s}   {mp.nstr(residual, 5):>12s}")
    (article_dir / "numerical_values.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        default="figures",
        help="directory for PDF figures (default: figures)",
    )
    args = parser.parse_args()

    article_dir = Path(__file__).resolve().parent
    out_dir = Path(args.output_dir)
    if not out_dir.is_absolute():
        out_dir = article_dir / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    make_real_branch_figure(out_dir)
    make_branch_point_error_figures(out_dir)
    make_asymptotic_error_figures(out_dir)
    make_bound_figure(out_dir)
    make_newton_figure(out_dir)
    make_pade_figure(out_dir)
    write_value_table(article_dir)

    print(f"Wrote figures to {out_dir}")
    print(f"Wrote table to {article_dir / 'numerical_values.txt'}")


if __name__ == "__main__":
    main()
