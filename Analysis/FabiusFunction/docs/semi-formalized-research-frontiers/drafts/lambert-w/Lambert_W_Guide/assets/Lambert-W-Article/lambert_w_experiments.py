#!/usr/bin/env python3
"""Numerical experiments and figures for the Lambert W monograph.

The script is deliberately self-contained.  It uses mpmath for high-precision
values of the two real branches, NumPy for sampling, and Matplotlib for figures.
It generates all figures and the small numerical table included by the LaTeX
source.  Running it again should reproduce the numerical artifacts in the ZIP.

The mathematical conventions are:

* W0(x) is the principal real branch on [-1/e, infinity).
* Wm1(x) is the lower real branch W_{-1}(x) on [-1/e, 0).
* Near the branch point, p = sqrt(2(1+e*x)).
* For W_{-1}(x) near zero, t = log(1/(-x)) and ell = log(t).

No random numbers are used, so the output is deterministic.
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Callable, Iterable, List, Sequence, Tuple

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parent
FIG = ROOT / "figures"
GEN = ROOT / "generated"
FIG.mkdir(exist_ok=True)
GEN.mkdir(exist_ok=True)

# Fifty decimal digits are more than enough for the plotted ranges and tables.
mp.mp.dps = 50
E = mp.e
BRANCH_POINT = -1 / E


# Coefficients c_n in U(p)=sum_{n>=1} c_n p^n, where
# W_0(x)=-1+U(p), W_{-1}(x)=-1+U(-p), p=sqrt(2(1+e*x)).
# They are obtained by series reversion of
#     p^2 = 2(1+(-1+u)e^u).
BRANCH_COEFFS: Tuple[mp.mpf, ...] = tuple(
    mp.mpf(n) / mp.mpf(d)
    for n, d in [
        (1, 1),
        (-1, 3),
        (11, 72),
        (-43, 540),
        (769, 17280),
        (-221, 8505),
        (680863, 43545600),
        (-1963, 204120),
        (226287557, 37623398400),
        (-5776369, 1515591000),
    ]
)


def w0(x: float | mp.mpf) -> mp.mpf:
    """High-precision real value of the principal branch."""
    return mp.re(mp.lambertw(mp.mpf(x), 0))


def wm1(x: float | mp.mpf) -> mp.mpf:
    """High-precision real value of the negative-one branch."""
    return mp.re(mp.lambertw(mp.mpf(x), -1))


def branch_point_series(x: float | mp.mpf, branch: int, terms: int = 8) -> mp.mpf:
    """Puiseux approximation near -1/e for branch 0 or -1.

    The same analytic series U is used on both branches.  Replacing p by -p
    automatically changes the signs of the odd powers and leaves the even
    powers unchanged.
    """
    xx = mp.mpf(x)
    if xx == BRANCH_POINT:
        return mp.mpf(-1)
    p = mp.sqrt(2 * (1 + E * xx))
    if branch == -1:
        p = -p
    elif branch != 0:
        raise ValueError("branch must be 0 or -1")
    total = mp.mpf(-1)
    for n, coefficient in enumerate(BRANCH_COEFFS[:terms], start=1):
        total += coefficient * p**n
    return total


def asymptotic_polynomials(ell: mp.mpf) -> Tuple[mp.mpf, ...]:
    """Return P_1(ell),...,P_6(ell) in the large-argument expansion.

    W_0(x) = L-ell + sum P_n(ell)/L^n, L=log x.
    The same polynomials, with alternating signs, govern W_{-1}(x) at 0-.
    """
    l = ell
    return (
        l,
        l * (l - 2) / 2,
        l * (2 * l**2 - 9 * l + 6) / 6,
        l * (3 * l**3 - 22 * l**2 + 36 * l - 12) / 12,
        l * (12 * l**4 - 125 * l**3 + 350 * l**2 - 300 * l + 60) / 60,
        l
        * (20 * l**5 - 274 * l**4 + 1125 * l**3 - 1700 * l**2 + 900 * l - 120)
        / 120,
    )


def w0_asymptotic(x: float | mp.mpf, order: int = 4) -> mp.mpf:
    """Truncated asymptotic expansion for W_0(x), x>1."""
    xx = mp.mpf(x)
    L = mp.log(xx)
    ell = mp.log(L)
    value = L - ell
    for n, polynomial in enumerate(asymptotic_polynomials(ell)[:order], start=1):
        value += polynomial / L**n
    return value


def wm1_asymptotic(x: float | mp.mpf, order: int = 4) -> mp.mpf:
    """Truncated asymptotic expansion for W_{-1}(x), x->0-."""
    xx = mp.mpf(x)
    t = mp.log(1 / (-xx))
    ell = mp.log(t)
    value = -t - ell
    for n, polynomial in enumerate(asymptotic_polynomials(ell)[:order], start=1):
        value -= ((-1) ** (n - 1)) * polynomial / t**n
    return value


def pade_11(x: float | mp.mpf) -> mp.mpf:
    """[1/1] Pade approximant at the origin: x/(1+x)."""
    xx = mp.mpf(x)
    return xx / (1 + xx)


def pade_22(x: float | mp.mpf) -> mp.mpf:
    """[2/2] Pade approximant at the origin."""
    xx = mp.mpf(x)
    return xx * (4 * xx + 3) / 3 / ((5 * xx**2 + 14 * xx + 6) / 6)


def schroeder_correction(x: float | mp.mpf, initial: float | mp.mpf, order: int = 2) -> mp.mpf:
    """Inverse-Taylor (Schroeder-type) correction about an initial value.

    Let h(w)=w*exp(w), z0=h(initial), and Delta=x-z0.  Taylor expansion of
    h^{-1} about z0 gives the displayed corrections.  Orders 1 and 2 are
    implemented because they are compact and already show the rapid gain.
    """
    xx = mp.mpf(x)
    y = mp.mpf(initial)
    delta = xx - y * mp.e**y
    corrected = y + mp.e ** (-y) * delta / (1 + y)
    if order >= 2:
        corrected -= mp.e ** (-2 * y) * (y + 2) * delta**2 / (2 * (1 + y) ** 3)
    return corrected


def log_newton_step(x: mp.mpf, y: mp.mpf) -> mp.mpf:
    """One Newton step for y+log(|y|)=log(|x|).

    Since x/y>0 on either real branch, the compact expression below is valid
    for W_0 on both sides of zero and for W_{-1}.
    """
    return y / (1 + y) * (1 + mp.log(x / y))


def log_newton_sequence(x: float | mp.mpf, branch: int, steps: int = 8) -> List[mp.mpf]:
    """Return successive logarithmic Newton iterates with branch-safe starts."""
    xx = mp.mpf(x)
    if branch == 0:
        if xx == 0:
            return [mp.mpf(0)] * (steps + 1)
        if xx > 0:
            # log(1+x) lies above W_0(x), is positive, and is never too large.
            y = mp.log1p(xx)
        else:
            # For -1/e<x<0, x lies above W_0(x) and belongs to (-1,0).
            y = xx
    elif branch == -1:
        if not (BRANCH_POINT < xx < 0):
            raise ValueError("W_{-1} requires -1/e < x < 0")
        q = -mp.log(-xx)
        # The inequality -W_{-1}(-e^{-q}) > q+log(q) proves this is above
        # the desired root (less negative) and below -1.
        y = -q - mp.log(q)
    else:
        raise ValueError("branch must be 0 or -1")

    values = [y]
    for _ in range(steps):
        y = log_newton_step(xx, y)
        values.append(y)
    return values


def halley_step(x: mp.mpf, y: mp.mpf) -> mp.mpf:
    """One Halley step for f(y)=y exp(y)-x."""
    ey = mp.e**y
    residual = y * ey - x
    denominator = ey * (y + 1) - (y + 2) * residual / (2 * y + 2)
    return y - residual / denominator


def relative_error(approximation: mp.mpf, exact: mp.mpf) -> float:
    """Relative error, with a safe absolute-error fallback at exact zero."""
    if exact == 0:
        return float(abs(approximation))
    return float(abs((approximation - exact) / exact))


def float_array(values: Iterable[mp.mpf]) -> np.ndarray:
    """Convert an iterable of mpmath numbers into a NumPy float array."""
    return np.asarray([float(v) for v in values], dtype=float)


def make_real_branches_figure() -> None:
    eps = 1e-7
    x0 = np.linspace(float(BRANCH_POINT) + eps, 6.0, 900)
    # A nonlinear parameter clusters points near both endpoints of W_{-1}.
    s = np.linspace(0.0, 1.0, 700)
    xm1 = float(BRANCH_POINT) + eps + (-(1e-5) - (float(BRANCH_POINT) + eps)) * s**1.7

    plt.figure(figsize=(7.2, 4.8))
    plt.plot(x0, float_array(w0(v) for v in x0), label=r"$W_0(x)$")
    plt.plot(xm1, float_array(wm1(v) for v in xm1), label=r"$W_{-1}(x)$")
    plt.axvline(float(BRANCH_POINT), linewidth=0.8, linestyle="--")
    plt.axhline(-1.0, linewidth=0.8, linestyle="--")
    plt.xlabel(r"$x$")
    plt.ylabel(r"$W(x)$")
    plt.ylim(-10, 2.2)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG / "real_branches.pdf")
    plt.close()


def make_branch_point_figure() -> None:
    delta = np.logspace(-12, -1, 240)
    xs = (delta - 1.0) / math.e
    p = np.sqrt(2.0 * delta)
    exact0 = float_array(w0(v) for v in xs)
    exactm1 = float_array(wm1(v) for v in xs)
    approx0_1 = -1 + p
    approx0_5 = float_array(branch_point_series(v, 0, 5) for v in xs)
    approxm1_5 = float_array(branch_point_series(v, -1, 5) for v in xs)

    plt.figure(figsize=(7.2, 4.8))
    plt.loglog(delta, np.abs(exact0 - approx0_1), label=r"$W_0$: one term")
    plt.loglog(delta, np.abs(exact0 - approx0_5), label=r"$W_0$: five terms")
    plt.loglog(delta, np.abs(exactm1 - approxm1_5), label=r"$W_{-1}$: five terms")
    plt.xlabel(r"$1+ex$")
    plt.ylabel("absolute error")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG / "branch_point_errors.pdf")
    plt.close()


def make_condition_figure() -> None:
    delta = np.logspace(-12, -0.02, 350)
    xs = (delta - 1.0) / math.e
    k0 = float_array(1 / abs(1 + w0(v)) for v in xs)
    km1 = float_array(1 / abs(1 + wm1(v)) for v in xs)

    plt.figure(figsize=(7.2, 4.8))
    plt.loglog(delta, k0, label=r"$W_0$")
    plt.loglog(delta, km1, label=r"$W_{-1}$")
    plt.loglog(delta, 1 / np.sqrt(2 * delta), linestyle="--", label=r"$1/\sqrt{2(1+ex)}$")
    plt.xlabel(r"$1+ex$")
    plt.ylabel(r"relative condition number $1/|1+W|$")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIG / "conditioning.pdf")
    plt.close()


def make_w0_approximation_figure() -> None:
    xs = np.logspace(-6, 8, 420)
    exact = [w0(v) for v in xs]
    initial = [mp.log1p(v) for v in xs]
    first = [schroeder_correction(v, y, 1) for v, y in zip(xs, initial)]
    second = [schroeder_correction(v, y, 2) for v, y in zip(xs, initial)]
    asym2 = [w0_asymptotic(v, 2) if v > math.e else mp.nan for v in xs]
    asym5 = [w0_asymptotic(v, 5) if v > math.e else mp.nan for v in xs]

    plt.figure(figsize=(7.2, 4.8))
    plt.loglog(xs, [relative_error(a, e) for a, e in zip(initial, exact)], label=r"$\log(1+x)$")
    plt.loglog(xs, [relative_error(a, e) for a, e in zip(first, exact)], label="one inverse-Taylor correction")
    plt.loglog(xs, [relative_error(a, e) for a, e in zip(second, exact)], label="two inverse-Taylor corrections")
    plt.loglog(xs, [relative_error(a, e) if not mp.isnan(a) else np.nan for a, e in zip(asym2, exact)], label="asymptotic, 2 corrections")
    plt.loglog(xs, [relative_error(a, e) if not mp.isnan(a) else np.nan for a, e in zip(asym5, exact)], label="asymptotic, 5 corrections")
    plt.xlabel(r"$x$")
    plt.ylabel("relative error")
    plt.ylim(1e-17, 1.0)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(FIG / "w0_approximation_errors.pdf")
    plt.close()


def make_wm1_approximation_figure() -> None:
    # Parameter u=-1-log(-x) maps the branch point to u=0 and x->0- to u->infinity.
    us = np.logspace(-10, 16, 430)
    xs = [-mp.e ** (-mp.mpf(u) - 1) for u in us]
    exact = [wm1(v) for v in xs]
    bp5 = [branch_point_series(v, -1, 5) for v in xs]
    leading = [mp.log(-v) - mp.log(-mp.log(-v)) for v in xs]
    asym3 = [wm1_asymptotic(v, 3) for v in xs]
    asym6 = [wm1_asymptotic(v, 6) for v in xs]

    plt.figure(figsize=(7.2, 4.8))
    plt.loglog(us, [relative_error(a, e) for a, e in zip(bp5, exact)], label="branch-point, five terms")
    plt.loglog(us, [relative_error(a, e) for a, e in zip(leading, exact)], label="two logarithms")
    plt.loglog(us, [relative_error(a, e) for a, e in zip(asym3, exact)], label="asymptotic, three corrections")
    plt.loglog(us, [relative_error(a, e) for a, e in zip(asym6, exact)], label="asymptotic, six corrections")
    plt.xlabel(r"$u=-1-\log(-x)$")
    plt.ylabel("relative error")
    plt.ylim(1e-17, 3.0)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(FIG / "wm1_approximation_errors.pdf")
    plt.close()


def make_iteration_figure() -> None:
    cases: Sequence[Tuple[float, int, str]] = [
        (10.0, 0, r"$W_0(10)$"),
        (-0.1, 0, r"$W_0(-0.1)$"),
        (-0.1, -1, r"$W_{-1}(-0.1)$"),
        (float(BRANCH_POINT + mp.mpf("1e-8")), -1, r"$W_{-1}(-1/e+10^{-8})$"),
    ]
    plt.figure(figsize=(7.2, 4.8))
    for x, branch, label in cases:
        exact = w0(x) if branch == 0 else wm1(x)
        sequence = log_newton_sequence(x, branch, 8)
        errors = [max(float(abs(y - exact)), 1e-50) for y in sequence]
        plt.semilogy(range(len(errors)), errors, marker="o", label=label)
    plt.xlabel("iteration number")
    plt.ylabel("absolute error")
    plt.ylim(1e-35, 10.0)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(FIG / "log_newton_convergence.pdf")
    plt.close()


def write_numerical_table() -> None:
    """Write a compact table of representative values in LaTeX syntax."""
    rows: Sequence[Tuple[str, mp.mpf, int]] = [
        (r"$-1/e$", BRANCH_POINT, 0),
        (r"$-1/e$", BRANCH_POINT, -1),
        (r"$-0.35$", mp.mpf("-0.35"), 0),
        (r"$-0.35$", mp.mpf("-0.35"), -1),
        (r"$-0.1$", mp.mpf("-0.1"), 0),
        (r"$-0.1$", mp.mpf("-0.1"), -1),
        (r"$-10^{-6}$", mp.mpf("-1e-6"), 0),
        (r"$-10^{-6}$", mp.mpf("-1e-6"), -1),
        (r"$0$", mp.mpf("0"), 0),
        (r"$0.1$", mp.mpf("0.1"), 0),
        (r"$1$", mp.mpf("1"), 0),
        (r"$e$", E, 0),
        (r"$10$", mp.mpf("10"), 0),
        (r"$10^6$", mp.mpf("1e6"), 0),
    ]
    lines = [
        r"\begin{tabular}{@{}rcr@{}}",
        r"\toprule",
        r"argument & branch & value \\",
        r"\midrule",
    ]
    for label, x, branch in rows:
        value = mp.mpf(-1) if x == BRANCH_POINT else (w0(x) if branch == 0 else wm1(x))
        branch_label = r"$W_0$" if branch == 0 else r"$W_{-1}$"
        lines.append(f"{label} & {branch_label} & ${mp.nstr(value, 15)}$" + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN / "representative_values.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_iteration_table() -> None:
    cases: Sequence[Tuple[str, mp.mpf, int]] = [
        (r"$10$", mp.mpf("10"), 0),
        (r"$-0.1$", mp.mpf("-0.1"), 0),
        (r"$-0.1$", mp.mpf("-0.1"), -1),
        (r"$-1/e+10^{-8}$", BRANCH_POINT + mp.mpf("1e-8"), -1),
        (r"$-10^{-30}$", mp.mpf("-1e-30"), -1),
    ]
    lines = [
        r"\begin{tabular}{@{}rcrr@{}}",
        r"\toprule",
        r"argument & branch & steps for $10^{-15}$ & final absolute error \\",
        r"\midrule",
    ]
    for label, x, branch in cases:
        exact = w0(x) if branch == 0 else wm1(x)
        sequence = log_newton_sequence(x, branch, 20)
        count = 20
        final_error = abs(sequence[-1] - exact)
        for i, y in enumerate(sequence):
            err = abs(y - exact)
            if err < mp.mpf("1e-15"):
                count = i
                final_error = err
                break
        branch_label = r"$W_0$" if branch == 0 else r"$W_{-1}$"
        lines.append(f"{label} & {branch_label} & {count} & ${mp.nstr(final_error, 4)}$" + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN / "iteration_counts.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    make_real_branches_figure()
    make_branch_point_figure()
    make_condition_figure()
    make_w0_approximation_figure()
    make_wm1_approximation_figure()
    make_iteration_figure()
    write_numerical_table()
    write_iteration_table()
    print(f"Generated figures in {FIG}")
    print(f"Generated LaTeX tables in {GEN}")


if __name__ == "__main__":
    main()
