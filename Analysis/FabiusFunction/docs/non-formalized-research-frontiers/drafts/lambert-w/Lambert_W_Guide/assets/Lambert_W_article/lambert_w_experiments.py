#!/usr/bin/env python3
"""Numerical experiments for the accompanying Lambert-W article.

The article is deliberately proof-oriented.  This script has a different role:
it checks numerical sizes, compares approximations, and generates the figures and
small tables used in the PDF.  Nothing in the proofs depends on floating-point
experiments.

Only freely available Python packages are used:

    mpmath      high-precision reference values and elementary functions
    numpy       plotting grids and convenient arrays
    matplotlib  publication-quality figures

Typical use (from the article directory):

    python lambert_w_experiments.py --output-dir .

The script writes PDF figures below ``figures/``, a CSV data table below
``data/``, and ``numerical_results.tex`` for inclusion in the LaTeX document.
The computations use 80 decimal digits internally.  Values are converted to
ordinary double precision only when passed to Matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


# High precision is useful near the branch point -1/e and near x=0 on W_{-1}.
# Eighty decimal digits are much more than the plotted accuracy requires, but
# make the reference values safely independent of ordinary double rounding.
mp.mp.dps = 80


# ---------------------------------------------------------------------------
# Reference branches and analytic approximations
# ---------------------------------------------------------------------------


def W0(x: mp.mpf) -> mp.mpf:
    """Return the real principal branch W_0(x)."""

    return mp.re(mp.lambertw(x, 0))


def Wm1(x: mp.mpf) -> mp.mpf:
    """Return the lower real branch W_{-1}(x), -1/e <= x < 0."""

    return mp.re(mp.lambertw(x, -1))


def pade_22(x: mp.mpf) -> mp.mpf:
    r"""The [2/2] Padé approximant at x=0.

    Matching the Taylor series

        W_0(x) = x - x^2 + 3 x^3/2 - 8 x^4/3 + ...

    through degree four gives

        x(1 + 4x/3) / (1 + 7x/3 + 5x^2/6).
    """

    return x * (1 + mp.mpf(4) * x / 3) / (
        1 + mp.mpf(7) * x / 3 + mp.mpf(5) * x * x / 6
    )


def iacono_positive_start(x: mp.mpf) -> mp.mpf:
    r"""Iacono--Boyd's simple starter for x>0.

    alpha(x) = 1 / (1 + (1/2) log(1+x)),
    w_0      = log(1 + alpha(x) x).

    It has the correct first two local Taylor terms and the correct first two
    logarithmic terms at infinity.
    """

    alpha = 1 / (1 + mp.log1p(x) / 2)
    return mp.log1p(alpha * x)


def iacono_global_start(x: mp.mpf) -> mp.mpf:
    r"""A global analytic starter for W_0 on [-1/e, infinity).

    This is equation (20) of Iacono and Boyd (2017).  The variable
    y=sqrt(1+e x) automatically builds in the square-root singularity at the
    real branch point.
    """

    y = mp.sqrt(1 + mp.e * x)
    # The paper prints rounded values b=1.14956131 and c=0.45495740.
    # Reconstructing b and c from the defining constraints makes the starter
    # interpolate W_0(0)=0 exactly instead of leaving a 7e-10 rounding offset.
    a = mp.mpf("2.036")
    exp_one_over_a = mp.exp(1 / a)
    c = (exp_one_over_a - 1 - mp.sqrt(2) / a) / (1 - exp_one_over_a * mp.log(2))
    b = mp.sqrt(2) / a + c
    numerator = 1 + b * y
    denominator = 1 + c * mp.log1p(y)
    return -1 + a * mp.log(numerator / denominator)


def log_newton(x: mp.mpf, w: mp.mpf) -> mp.mpf:
    r"""One logarithmic Newton step.

    Newton's method is applied to

        F(w) = w + log|w| - log|x| = 0.

    The algebraically simplified update is

        w_new = w/(1+w) * (1 + log(x/w)),

    where x/w is positive on either real branch.  Unlike Newton applied to
    w exp(w)-x, this form does not construct exp(w) and is therefore attractive
    for very large positive arguments.
    """

    if x == 0:
        return mp.mpf(0)
    if w == 0 or x / w <= 0:
        raise ValueError("logarithmic Newton requires x/w > 0 and w != 0")
    if w == -1:
        raise ValueError("the Newton derivative vanishes at w=-1")
    return (w / (1 + w)) * (1 + mp.log(x / w))


def newton_original(x: mp.mpf, w: mp.mpf) -> mp.mpf:
    r"""One Newton step for f(w)=w exp(w)-x.

    The exp(-w) form avoids one multiplication by exp(w), but may overflow for
    a very negative trial value.  It is used only on moderate examples here.
    """

    if w == -1:
        raise ValueError("the Newton derivative vanishes at w=-1")
    return w - (w - x * mp.exp(-w)) / (1 + w)


def halley(x: mp.mpf, w: mp.mpf) -> mp.mpf:
    r"""One Halley step for f(w)=w exp(w)-x."""

    ew = mp.exp(w)
    f = w * ew - x
    fp = ew * (1 + w)
    fpp = ew * (2 + w)
    denominator = fp - f * fpp / (2 * fp)
    return w - f / denominator


# Coefficients c_n in
#
#     W = -1 + sum_{n>=1} c_n p^n,
#
# where p=+sqrt(2(1+ex)) on W_0 and p=-sqrt(2(1+ex)) on W_{-1}.
# The same coefficients therefore serve both real branches.
PUISEUX_COEFFICIENTS: tuple[mp.mpf, ...] = (
    mp.mpf(1),
    -mp.mpf(1) / 3,
    mp.mpf(11) / 72,
    -mp.mpf(43) / 540,
    mp.mpf(769) / 17280,
    -mp.mpf(221) / 8505,
    mp.mpf(680863) / 43545600,
    -mp.mpf(1963) / 204120,
)


def puiseux(x: mp.mpf, branch: int, order: int = 8) -> mp.mpf:
    r"""Truncate the branch-point Puiseux series after p**order.

    ``branch`` must be 0 or -1.  The formula is intended for x close to -1/e.
    """

    if branch not in (0, -1):
        raise ValueError("branch must be 0 or -1")
    if not (-1 / mp.e <= x < 0):
        raise ValueError("real Puiseux formula requires -1/e <= x < 0")
    if not (1 <= order <= len(PUISEUX_COEFFICIENTS)):
        raise ValueError("unsupported truncation order")
    sign = 1 if branch == 0 else -1
    p = sign * mp.sqrt(2 * (1 + mp.e * x))
    total = mp.mpf(-1)
    power = mp.mpf(1)
    for coefficient in PUISEUX_COEFFICIENTS[:order]:
        power *= p
        total += coefficient * power
    return total


def asymptotic_real(x: mp.mpf, branch: int, order: int = 4) -> mp.mpf:
    r"""Truncate the classical logarithmic expansion.

    For branch 0 this is used as x -> +infinity:

        L1=log(x),       L2=log(L1).

    For branch -1 this is used as x -> 0 from below:

        L1=log(-x)<0,    L2=log(-L1).

    ``order`` counts correction polynomials after L1-L2.  Values 0 through 4
    are implemented explicitly.
    """

    if branch == 0:
        if x <= 1:
            raise ValueError("the positive asymptotic implementation expects x>1")
        L1 = mp.log(x)
        L2 = mp.log(L1)
    elif branch == -1:
        if not (-1 / mp.e < x < 0):
            raise ValueError("W_-1 asymptotic implementation expects -1/e<x<0")
        L1 = mp.log(-x)
        L2 = mp.log(-L1)
    else:
        raise ValueError("branch must be 0 or -1")

    result = L1 - L2
    if order >= 1:
        result += L2 / L1
    if order >= 2:
        result += L2 * (-2 + L2) / (2 * L1**2)
    if order >= 3:
        result += L2 * (6 - 9 * L2 + 2 * L2**2) / (6 * L1**3)
    if order >= 4:
        result += L2 * (-12 + 36 * L2 - 22 * L2**2 + 3 * L2**3) / (
            12 * L1**4
        )
    if not (0 <= order <= 4):
        raise ValueError("order must be between 0 and 4")
    return result


def wm1_chatzigeorgiou_bounds(x: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    r"""Return rigorous lower and upper bounds for W_{-1}(x).

    Write x=-exp(-u-1), u>0.  Chatzigeorgiou's inequalities are

        -1-sqrt(2u)-u < W_{-1}(x)
                         < -1-sqrt(2u)-(2/3)u.

    The first number returned is the lower (more negative) bound.
    """

    if not (-1 / mp.e < x < 0):
        raise ValueError("bounds require -1/e < x < 0")
    u = -1 - mp.log(-x)
    lower = -1 - mp.sqrt(2 * u) - u
    upper = -1 - mp.sqrt(2 * u) - mp.mpf(2) * u / 3
    return lower, upper


def scaled_error(approximation: mp.mpf, exact: mp.mpf) -> mp.mpf:
    r"""A zero-safe error: |a-e|/(1+|e|)."""

    return abs(approximation - exact) / (1 + abs(exact))


def relative_error(approximation: mp.mpf, exact: mp.mpf) -> mp.mpf:
    """Ordinary relative error, used only where the exact value is nonzero."""

    return abs(approximation - exact) / abs(exact)


# ---------------------------------------------------------------------------
# Plotting utilities
# ---------------------------------------------------------------------------


def save_figure(path: Path) -> None:
    """Finish and save the current Matplotlib figure."""

    path.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(path, bbox_inches="tight")
    plt.close()


def mp_values(function: Callable[[mp.mpf], mp.mpf], xs: Iterable[float]) -> np.ndarray:
    """Evaluate an mpmath function on a plotting grid and return float values."""

    return np.array([float(function(mp.mpf(str(x)))) for x in xs], dtype=float)


def plot_real_branches(figures: Path) -> None:
    """Plot both real branches with a magnified negative-x domain."""

    branch_point = -1 / math.e
    x0_negative = np.linspace(branch_point, -1.0e-5, 700)
    x0_positive = np.linspace(0.0, 8.0, 600)
    xm1 = -np.geomspace(1.0e-7, 1 / math.e, 700)[::-1]

    plt.figure(figsize=(7.1, 4.5))
    plt.plot(x0_negative, mp_values(W0, x0_negative), label=r"$W_0(x)$")
    plt.plot(x0_positive, mp_values(W0, x0_positive), label=r"$W_0(x)$")
    plt.plot(xm1, mp_values(Wm1, xm1), label=r"$W_{-1}(x)$")
    plt.axhline(0.0, linewidth=0.7)
    plt.axvline(0.0, linewidth=0.7)
    plt.scatter([branch_point], [-1.0], zorder=5)
    plt.xlabel(r"$x$")
    plt.ylabel(r"$W(x)$")
    plt.ylim(-12, 2.0)
    plt.legend()
    plt.grid(True, linewidth=0.35)
    save_figure(figures / "real_branches.pdf")


def plot_puiseux_errors(figures: Path) -> None:
    """Show how the shared signed-p series approximates both real branches."""

    # Parameterizing by eta=1+e*x gives many points very close to the branch
    # point without catastrophic subtraction in the plotting grid.
    etas = np.geomspace(1.0e-14, 0.35, 500)
    xs = (etas - 1) / math.e

    plt.figure(figsize=(7.1, 4.5))
    for branch, branch_label in ((0, "0"), (-1, "-1")):
        exact = np.array(
            [float(W0(mp.mpf(str(x))) if branch == 0 else Wm1(mp.mpf(str(x)))) for x in xs]
        )
        for order in (2, 4, 6, 8):
            approximate = np.array(
                [float(puiseux(mp.mpf(str(x)), branch, order)) for x in xs]
            )
            error = np.abs(approximate - exact) / (1 + np.abs(exact))
            plt.loglog(
                etas,
                error,
                label=rf"$W_{{{branch_label}}}$, through $p^{{{order}}}$",
            )
    plt.xlabel(r"$1+ex$")
    plt.ylabel(r"scaled error $|\widetilde W-W|/(1+|W|)$")
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(ncol=2, fontsize=8)
    save_figure(figures / "puiseux_errors.pdf")


def plot_asymptotic_w0(figures: Path) -> None:
    """Plot errors of successive positive-infinity asymptotic truncations."""

    xs = np.geomspace(10.0, 1.0e50, 420)
    exact = np.array([float(W0(mp.mpf(str(x)))) for x in xs])

    plt.figure(figsize=(7.1, 4.5))
    for order in range(0, 5):
        approximate = np.array(
            [float(asymptotic_real(mp.mpf(str(x)), 0, order)) for x in xs]
        )
        error = np.abs(approximate - exact) / np.abs(exact)
        plt.loglog(xs, error, label=rf"{order} correction term(s)")
    plt.xlabel(r"$x$")
    plt.ylabel(r"relative error on $W_0(x)$")
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(fontsize=8)
    save_figure(figures / "asymptotic_errors_w0.pdf")


def plot_asymptotic_wm1(figures: Path) -> None:
    """Plot errors of the x->0- asymptotic expansion of W_{-1}."""

    magnitudes = np.geomspace(1.0e-60, 1.0e-2, 420)
    xs = -magnitudes
    exact = np.array([float(Wm1(mp.mpf(str(x)))) for x in xs])

    plt.figure(figsize=(7.1, 4.5))
    for order in range(0, 5):
        approximate = np.array(
            [float(asymptotic_real(mp.mpf(str(x)), -1, order)) for x in xs]
        )
        error = np.abs(approximate - exact) / np.abs(exact)
        plt.loglog(magnitudes, error, label=rf"{order} correction term(s)")
    plt.xlabel(r"$|x|$ (approaching zero to the left)")
    plt.ylabel(r"relative error on $W_{-1}(x)$")
    plt.gca().invert_xaxis()
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(fontsize=8)
    save_figure(figures / "asymptotic_errors_wm1.pdf")


def plot_global_approximation(figures: Path) -> None:
    """Compare a global starter and successive logarithmic Newton corrections."""

    # Use eta=1+e*x for the negative side and a logarithmic grid for x>0.
    negative_etas = np.geomspace(1.0e-14, 1.0, 300)
    negative_x = (negative_etas - 1) / math.e
    positive_x = np.concatenate(([0.0], np.geomspace(1.0e-12, 1.0e18, 440)))
    xs = np.concatenate((negative_x[:-1], positive_x))

    exact = np.array([float(W0(mp.mpf(str(x)))) for x in xs])
    starts: list[np.ndarray] = []

    for iterations in range(4):
        values: list[float] = []
        for x_float in xs:
            x = mp.mpf(str(x_float))
            w = iacono_global_start(x)
            if x == 0:
                w = mp.mpf(0)
            else:
                for _ in range(iterations):
                    w = log_newton(x, w)
            values.append(float(w))
        starts.append(np.array(values))

    # A transformed abscissa gives one readable graph for the entire branch.
    # z=sign(x)*log10(1+|x|) keeps x=0 finite and separates negative x.
    z = np.sign(xs) * np.log10(1 + np.abs(xs))

    plt.figure(figsize=(7.1, 4.5))
    for iterations, approximate in enumerate(starts):
        error = np.abs(approximate - exact) / (1 + np.abs(exact))
        label = "global starter" if iterations == 0 else rf"after {iterations} log-Newton step(s)"
        plt.semilogy(z, np.maximum(error, 1.0e-80), label=label)
    plt.xlabel(r"signed compressed coordinate $\operatorname{sgn}(x)\log_{10}(1+|x|)$")
    plt.ylabel(r"scaled error $|\widetilde W-W_0|/(1+|W_0|)$")
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(fontsize=8)
    save_figure(figures / "global_approximation_errors.pdf")


def plot_iteration_convergence(figures: Path) -> None:
    """Compare Newton, Halley, and logarithmic Newton on representative inputs."""

    cases: Sequence[tuple[str, mp.mpf, int, mp.mpf]] = (
        (r"$W_0(10^{20})$", mp.mpf("1e20"), 0, iacono_positive_start(mp.mpf("1e20"))),
        (r"$W_0(-0.3)$", mp.mpf("-0.3"), 0, iacono_global_start(mp.mpf("-0.3"))),
        (r"$W_{-1}(-10^{-20})$", mp.mpf("-1e-20"), -1, asymptotic_real(mp.mpf("-1e-20"), -1, 1)),
    )

    plt.figure(figsize=(7.1, 4.5))
    for case_label, x, branch, start in cases:
        exact = W0(x) if branch == 0 else Wm1(x)
        for method_name, method in (
            ("Newton", newton_original),
            ("Halley", halley),
            ("log-Newton", log_newton),
        ):
            w = start
            errors = [float(scaled_error(w, exact))]
            for _ in range(6):
                try:
                    w = method(x, w)
                    errors.append(float(scaled_error(w, exact)))
                except (ValueError, ZeroDivisionError):
                    errors.append(float("nan"))
                    break
            plt.semilogy(
                range(len(errors)),
                np.maximum(np.array(errors), 1.0e-80),
                marker="o",
                markersize=3,
                label=f"{case_label}: {method_name}",
            )
    plt.xlabel("iteration number")
    plt.ylabel(r"scaled error $|w_n-W|/(1+|W|)$")
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(fontsize=7, ncol=2)
    save_figure(figures / "iteration_convergence.pdf")


def plot_condition_numbers(figures: Path) -> None:
    r"""Plot the relative condition number |1/(1+W)| on both real branches."""

    eta = np.geomspace(1.0e-12, 0.999999, 380)
    x_negative = (eta - 1) / math.e
    x_positive = np.geomspace(1.0e-10, 1.0e20, 380)

    w0_negative = np.array([float(W0(mp.mpf(str(x)))) for x in x_negative])
    wm1_negative = np.array([float(Wm1(mp.mpf(str(x)))) for x in x_negative])
    w0_positive = np.array([float(W0(mp.mpf(str(x)))) for x in x_positive])

    plt.figure(figsize=(7.1, 4.5))
    plt.loglog(eta, np.abs(1 / (1 + w0_negative)), label=r"$W_0$, negative side")
    plt.loglog(eta, np.abs(1 / (1 + wm1_negative)), label=r"$W_{-1}$")
    plt.loglog(1 + x_positive, np.abs(1 / (1 + w0_positive)), label=r"$W_0$, positive side")
    plt.xlabel(r"distance-like coordinate: $1+ex$ (negative side) or $1+x$ (positive side)")
    plt.ylabel(r"relative condition number $|1/(1+W)|$")
    plt.grid(True, which="both", linewidth=0.35)
    plt.legend(fontsize=8)
    save_figure(figures / "condition_numbers.pdf")


# ---------------------------------------------------------------------------
# Tables and reproducible numerical summaries
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ExperimentResult:
    description: str
    domain: str
    error_measure: str
    maximum_error: mp.mpf


def maximum_on_grid(
    xs: Iterable[mp.mpf],
    exact: Callable[[mp.mpf], mp.mpf],
    approximate: Callable[[mp.mpf], mp.mpf],
    measure: Callable[[mp.mpf, mp.mpf], mp.mpf],
) -> mp.mpf:
    """Compute a sampled maximum; this is an experiment, not a certified bound."""

    maximum = mp.mpf(0)
    for x in xs:
        value = measure(approximate(x), exact(x))
        if value > maximum:
            maximum = value
    return maximum


def geometric_mpf(start_exp: float, stop_exp: float, count: int) -> list[mp.mpf]:
    """Return base-10 logarithmically spaced positive mpmath numbers."""

    return [mp.power(10, start_exp + (stop_exp - start_exp) * i / (count - 1)) for i in range(count)]


def build_experiment_table() -> list[ExperimentResult]:
    """Run the sampled comparisons reported in the article."""

    results: list[ExperimentResult] = []

    positive_grid = geometric_mpf(-12, 18, 1600)

    results.append(
        ExperimentResult(
            "Iacono--Boyd positive starter",
            r"$10^{-12}\le x\le10^{18}$",
            "relative",
            maximum_on_grid(positive_grid, W0, iacono_positive_start, relative_error),
        )
    )

    def positive_after_steps(x: mp.mpf, steps: int) -> mp.mpf:
        w = iacono_positive_start(x)
        for _ in range(steps):
            w = log_newton(x, w)
        return w

    for steps in (1, 2, 3):
        results.append(
            ExperimentResult(
                f"positive starter + {steps} log-Newton step(s)",
                r"$10^{-12}\le x\le10^{18}$",
                "relative",
                maximum_on_grid(
                    positive_grid,
                    W0,
                    lambda x, steps=steps: positive_after_steps(x, steps),
                    relative_error,
                ),
            )
        )

    # The global branch includes W_0(0)=0, so a zero-safe scaled error is more
    # informative than relative error.  The grid is dense in eta=1+ex near the
    # square-root branch point and logarithmic for positive x.
    negative_grid = [
        (mp.power(10, -14 + 14 * i / 799) - 1) / mp.e for i in range(800)
    ]
    global_grid = negative_grid + [mp.mpf(0)] + positive_grid

    results.append(
        ExperimentResult(
            "Iacono--Boyd global starter",
            r"$-1/e+10^{-14}/e\le x\le10^{18}$",
            "scaled",
            maximum_on_grid(global_grid, W0, iacono_global_start, scaled_error),
        )
    )

    pade_grid = [mp.mpf("-0.25") + mp.mpf("0.5") * i / 1600 for i in range(1601)]
    results.append(
        ExperimentResult(
            r"$[2/2]$ Pad\'e approximant",
            r"$-0.25\le x\le0.25$",
            "scaled",
            maximum_on_grid(pade_grid, W0, pade_22, scaled_error),
        )
    )

    # Puiseux grids are parameterized by eta=1+ex; the branch point itself is
    # excluded from relative comparisons but causes no issue for scaled error.
    puiseux_grid = [
        (mp.power(10, -14 + (mp.log10(mp.mpf("0.25")) + 14) * i / 999) - 1)
        / mp.e
        for i in range(1000)
    ]
    for branch, label, exact in ((0, "W_0", W0), (-1, "W_{-1}", Wm1)):
        results.append(
            ExperimentResult(
                rf"Puiseux series through $p^8$ on ${label}$",
                r"$10^{-14}\le1+ex\le0.25$",
                "scaled",
                maximum_on_grid(
                    puiseux_grid,
                    exact,
                    lambda x, branch=branch: puiseux(x, branch, 8),
                    scaled_error,
                ),
            )
        )

    w0_asymptotic_grid = geometric_mpf(6, 50, 900)
    results.append(
        ExperimentResult(
            r"four-correction asymptotic expansion of $W_0$",
            r"$10^6\le x\le10^{50}$",
            "relative",
            maximum_on_grid(
                w0_asymptotic_grid,
                W0,
                lambda x: asymptotic_real(x, 0, 4),
                relative_error,
            ),
        )
    )

    wm1_asymptotic_grid = [-x for x in geometric_mpf(-60, -6, 900)]
    results.append(
        ExperimentResult(
            r"four-correction asymptotic expansion of $W_{-1}$",
            r"$10^{-60}\le|x|\le10^{-6}$",
            "relative",
            maximum_on_grid(
                wm1_asymptotic_grid,
                Wm1,
                lambda x: asymptotic_real(x, -1, 4),
                relative_error,
            ),
        )
    )

    # Measure how narrow the rigorous W_{-1} bracket is relative to 1+|W|.
    bound_grid = [
        -mp.e ** (-1 - u)
        for u in geometric_mpf(-10, 10, 1300)
    ]

    def bracket_width(x: mp.mpf) -> mp.mpf:
        lower, upper = wm1_chatzigeorgiou_bounds(x)
        return (upper - lower) / (1 + abs(Wm1(x)))

    maximum_width = max(bracket_width(x) for x in bound_grid)
    results.append(
        ExperimentResult(
            r"relative width of the rigorous $W_{-1}$ bracket",
            r"$10^{-10}\le u=-1-\log(-x)\le10^{10}$",
            "scaled width",
            maximum_width,
        )
    )

    return results


def tex_scientific(value: mp.mpf, digits: int = 4) -> str:
    """Format a positive mpmath number as LaTeX scientific notation."""

    if value == 0:
        return "$0$"
    exponent = int(mp.floor(mp.log10(abs(value))))
    mantissa = value / mp.power(10, exponent)
    mantissa_text = mp.nstr(mantissa, digits)
    return rf"${mantissa_text}\times 10^{{{exponent}}}$"


def write_results(output_dir: Path, results: Sequence[ExperimentResult]) -> None:
    """Write both a human-readable LaTeX table and a machine-readable CSV."""

    tex_path = output_dir / "numerical_results.tex"
    with tex_path.open("w", encoding="utf-8") as stream:
        stream.write("% Generated by lambert_w_experiments.py; do not edit by hand.\n")
        stream.write("\\begin{table}[tbp]\n")
        stream.write("\\centering\n")
        stream.write("\\caption{Sampled numerical errors. These are reproducible experimental maxima on the stated grids, not certified uniform bounds.}\n")
        stream.write("\\label{tab:numerical-experiments}\n")
        stream.write("\\small\n")
        stream.write("\\begin{tabularx}{\\textwidth}{@{}Xllr@{}}\n")
        stream.write("\\toprule\n")
        stream.write("Approximation or quantity & Sampled domain & Measure & Maximum \\\\\n")
        stream.write("\\midrule\n")
        for row in results:
            stream.write(
                f"{row.description} & {row.domain} & {row.error_measure} & "
                f"{tex_scientific(row.maximum_error)} \\\\\n"
            )
        stream.write("\\bottomrule\n")
        stream.write("\\end{tabularx}\n")
        stream.write("\\end{table}\n")

    csv_path = output_dir / "data" / "numerical_results.csv"
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(("description", "domain", "error_measure", "maximum_error"))
        for row in results:
            writer.writerow(
                (
                    row.description,
                    row.domain,
                    row.error_measure,
                    mp.nstr(row.maximum_error, 30),
                )
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory that will receive figures/, data/, and numerical_results.tex",
    )
    arguments = parser.parse_args()

    output_dir = arguments.output_dir.resolve()
    figures = output_dir / "figures"
    figures.mkdir(parents=True, exist_ok=True)

    plot_real_branches(figures)
    plot_puiseux_errors(figures)
    plot_asymptotic_w0(figures)
    plot_asymptotic_wm1(figures)
    plot_global_approximation(figures)
    plot_iteration_convergence(figures)
    plot_condition_numbers(figures)

    results = build_experiment_table()
    write_results(output_dir, results)

    print(f"Wrote {len(results)} numerical summaries to {output_dir}")
    for result in results:
        print(f"  {result.description}: {mp.nstr(result.maximum_error, 8)}")


if __name__ == "__main__":
    main()
