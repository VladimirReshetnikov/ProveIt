#!/usr/bin/env python3
"""Numerical and symbolic experiments for the inverse q-analogs report.

The program is deliberately self-contained.  It validates several formulas
proved in the accompanying LaTeX report and generates all numerical tables and
figures used there.  It does *not* use black-box inverse-q special functions:
branches are selected explicitly and inverse values are obtained by safeguarded
root finding or by continuation from a prescribed initial point.

Main experiments
----------------
1. The exact q=-1 critical locus of the finite q-Pochhammer polynomial.
2. Regular, square-root, and cubic inverse branches near q=-1.
3. Reversion of Gaussian (q-binomial) coefficients at q=0, 1, -1, and infinity.
4. Radial inversion of (a;q)_infinity as q approaches 1 and -1.
5. The q->0 Newton-polygon regimes of Gamma_q(x).
6. Exact recovery of the geometric parameter in a generalized Rvachev/Fabius
   random series from its variance and higher cumulants.

Dependencies: Python 3.10+, mpmath, sympy, numpy, matplotlib.
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
import sympy as sp


MP_DPS = 80
mp.mp.dps = MP_DPS


# ---------------------------------------------------------------------------
# Elementary q-products and q-polynomials
# ---------------------------------------------------------------------------

def finite_qpoch(a: complex | mp.mpf | mp.mpc,
                  q: complex | mp.mpf | mp.mpc,
                  n: int) -> mp.mpf | mp.mpc:
    """Return (a;q)_n by direct multiplication.

    Direct multiplication is preferable here because n is small in all branch
    experiments and it avoids hidden choices made by special-function code.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    p = mp.mpf(1)
    for j in range(n):
        p *= 1 - a * q**j
    return p


def gaussian_binomial(n: int, k: int,
                      q: complex | mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Evaluate the Gaussian coefficient [n choose k]_q stably.

    Near roots of unity the quotient-of-products formula has removable 0/0
    singularities.  The coefficient recurrence produces the polynomial value
    directly and is therefore valid at every complex q.
    """
    if k < 0 or k > n:
        return mp.mpf(0)
    k = min(k, n - k)
    row = [mp.mpf(0)] * (k + 1)
    row[0] = mp.mpf(1)
    for nn in range(1, n + 1):
        upper = min(nn, k)
        for kk in range(upper, 0, -1):
            row[kk] = row[kk] + q ** (nn - kk) * row[kk - 1]
    return row[k]


def q_factorial(n: int, q: complex | mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return [n]_q! as a polynomial evaluation."""
    p = mp.mpf(1)
    for j in range(1, n + 1):
        # This finite sum remains well conditioned at q=1 and roots of unity.
        qj = mp.fsum(q**r for r in range(j))
        p *= qj
    return p


def log_qpoch_infinite_lambert(a: complex | mp.mpf | mp.mpc,
                                q: complex | mp.mpf | mp.mpc,
                                tol: mp.mpf | None = None,
                                max_terms: int = 2_000_000) -> mp.mpf | mp.mpc:
    r"""Compute log (a;q)_infinity from its Lambert series.

        log (a;q)_infinity = - sum_{r>=1} a^r/[r(1-q^r)].

    This representation is exceptionally effective for |a|<1, even when q is
    close to a root of unity: convergence is then controlled primarily by a^r.
    The branch of the logarithm is the one obtained continuously from a=0.
    """
    if abs(q) >= 1:
        raise ValueError("Lambert series requires |q|<1")
    if abs(a) >= 1:
        raise ValueError("This implementation is intended for |a|<1")
    if tol is None:
        tol = mp.mpf(10) ** (-(MP_DPS - 15))
    total = mp.mpc(0) if (isinstance(a, (complex, mp.mpc)) or
                           isinstance(q, (complex, mp.mpc))) else mp.mpf(0)
    ar = mp.mpf(1)
    for r in range(1, max_terms + 1):
        ar *= a
        term = -ar / (r * (1 - q**r))
        total += term
        # Require several harmlessly tiny terms; this avoids stopping at an
        # accidental small numerator in a complex oscillatory series.
        if r > 20 and abs(term) < tol * max(1, abs(total)):
            tail_bound = abs(ar * a) / ((r + 1) * max(mp.mpf("1e-50"), 1 - abs(q)**(r + 1)))
            tail_bound /= max(mp.mpf("1e-50"), 1 - abs(a))
            if tail_bound < 10 * tol * max(1, abs(total)):
                return total
    raise RuntimeError("Lambert series did not converge within max_terms")


def log_qgamma(x: mp.mpf, q: mp.mpf) -> mp.mpf:
    r"""Evaluate log Gamma_q(x), 0<q<1, from Lambert series.

    The formula is
      log Gamma_q(x) = (1-x)log(1-q)
                       + log(q;q)_infinity - log(q^x;q)_infinity.
    The two infinite-product logarithms are summed together term by term to
    reduce cancellation when q is close to one.
    """
    if not (0 < q < 1 and x > 0):
        raise ValueError("require 0<q<1 and x>0")
    tol = mp.mpf(10) ** (-(MP_DPS - 15))
    total = (1 - x) * mp.log1p(-q)
    for r in range(1, 2_000_000):
        term = (q ** (x * r) - q**r) / (r * (1 - q**r))
        total += term
        if r > 30 and abs(term) < tol * max(1, abs(total)):
            return total
    raise RuntimeError("q-gamma Lambert series did not converge")


# ---------------------------------------------------------------------------
# Generic scalar inversion helpers
# ---------------------------------------------------------------------------

def bisect_monotone(f: Callable[[mp.mpf], mp.mpf], target: mp.mpf,
                    lo: mp.mpf, hi: mp.mpf, *, increasing: bool = True,
                    iterations: int = 300) -> mp.mpf:
    """Invert a monotone real function on an explicitly supplied bracket."""
    flo = f(lo) - target
    fhi = f(hi) - target
    if increasing:
        if not (flo <= 0 <= fhi):
            raise ValueError(f"invalid increasing bracket: {flo=}, {fhi=}")
    else:
        if not (flo >= 0 >= fhi):
            raise ValueError(f"invalid decreasing bracket: {flo=}, {fhi=}")
    for _ in range(iterations):
        mid = (lo + hi) / 2
        fm = f(mid) - target
        if (fm < 0) == increasing:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def newton_continuation(f: Callable[[mp.mpf | mp.mpc], mp.mpf | mp.mpc],
                        df: Callable[[mp.mpf | mp.mpc], mp.mpf | mp.mpc],
                        target: mp.mpf | mp.mpc,
                        seed: mp.mpf | mp.mpc,
                        max_iter: int = 80) -> mp.mpf | mp.mpc:
    """Newton iteration with step damping, preserving a chosen local sheet."""
    x = seed
    old_res = abs(f(x) - target)
    for _ in range(max_iter):
        derivative = df(x)
        if derivative == 0:
            raise ZeroDivisionError("Newton iteration reached a critical point")
        step = (f(x) - target) / derivative
        damping = mp.mpf(1)
        accepted = False
        for _ in range(30):
            candidate = x - damping * step
            res = abs(f(candidate) - target)
            if res <= old_res or res < mp.mpf("1e-60"):
                x = candidate
                old_res = res
                accepted = True
                break
            damping /= 2
        if not accepted:
            raise RuntimeError("damped Newton step failed")
        if old_res < mp.mpf("1e-60"):
            return x
    return x


# ---------------------------------------------------------------------------
# q=-1 critical locus for finite q-Pochhammer products
# ---------------------------------------------------------------------------

def critical_a_at_minus_one(n: int) -> mp.mpf:
    """Distinguished a for which d/dq (a;q)_n vanishes at q=-1."""
    if n < 2:
        raise ValueError("n must be at least 2")
    return mp.mpf(1) / (n - 1) if n % 2 == 0 else -mp.mpf(1) / n


def symbolic_minus_one_table(max_n: int = 12) -> list[dict[str, str]]:
    """Use exact SymPy algebra to verify the critical and degeneracy formulas."""
    q, a = sp.symbols("q a")
    rows: list[dict[str, str]] = []
    # n=2 gives a_*=1, for which the entire product is identically zero;
    # the nondegenerate critical classification therefore begins at n=3.
    for n in range(3, max_n + 1):
        astar = sp.Rational(1, n - 1) if n % 2 == 0 else -sp.Rational(1, n)
        polynomial = sp.prod(1 - a * q**j for j in range(n))
        specialized = sp.expand(polynomial.subs(a, astar))
        f0 = sp.simplify(specialized.subs(q, -1))
        derivatives = [sp.simplify(sp.diff(specialized, q, r).subs(q, -1))
                       for r in range(1, 5)]
        order = next((r for r, d in enumerate(derivatives, start=1) if d != 0), None)
        rows.append({
            "n": str(n),
            "a_star": str(astar),
            "F_minus_one": str(f0),
            "first_nonzero_derivative_order": str(order),
            "F1": str(derivatives[0]),
            "F2": str(derivatives[1]),
            "F3": str(derivatives[2]),
            "F4": str(derivatives[3]),
        })
    return rows


def make_minus_one_figure(out_dir: Path) -> None:
    """Plot the quadratic and exceptional cubic critical inverse geometries."""
    q_values = np.linspace(-1.55, -0.45, 900)

    fig = plt.figure(figsize=(7.2, 4.6))
    ax = fig.add_subplot(111)
    for n, a, label in [
        (6, 1 / 5, r"$n=6,\ a=1/5$ (quadratic)"),
        (3, -1 / 3, r"$n=3,\ a=-1/3$ (cubic)"),
    ]:
        values = [float(finite_qpoch(mp.mpf(a), mp.mpf(q), n)) for q in q_values]
        f0 = float(finite_qpoch(mp.mpf(a), mp.mpf(-1), n))
        ax.plot(q_values, np.asarray(values) - f0, label=label)
    ax.axhline(0.0, linewidth=0.8)
    ax.axvline(-1.0, linewidth=0.8)
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"$(a;q)_n-(a;-1)_n$")
    ax.set_title(r"Critical finite $q$-Pochhammer branches at $q=-1$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "pochhammer_minus_one_critical.png", dpi=220)
    fig.savefig(out_dir / "pochhammer_minus_one_critical.pdf")
    plt.close(fig)


def make_n3_morse_figure(out_dir: Path) -> None:
    """Show that the exceptional cubic q-slice lies in a two-variable saddle.

    At (a,q)=(-1/3,-1), both first derivatives of (a;q)_3 vanish.  The
    Hessian in (a,q) is nevertheless nonsingular and indefinite.  The line
    a=-1/3 happens to be tangent to a null direction of its quadratic part,
    so restriction to that line begins cubically.
    """
    a0, q0 = -1 / 3, -1.0
    av = np.linspace(-0.62, -0.04, 520)
    qv = np.linspace(-1.42, -0.58, 520)
    A, Q = np.meshgrid(av, qv)
    F = (1 - A) * (1 - A * Q) * (1 - A * Q**2)
    F0 = (1 - a0) * (1 - a0 * q0) * (1 - a0 * q0**2)
    Z = F - F0

    fig = plt.figure(figsize=(7.2, 5.0))
    ax = fig.add_subplot(111)
    levels = np.array([-0.08, -0.04, -0.015, -0.005, 0.0,
                       0.005, 0.015, 0.04, 0.08])
    contours = ax.contour(A, Q, Z, levels=levels, linewidths=1.0)
    ax.clabel(contours, inline=True, fontsize=7, fmt=lambda x: f"{x:.3g}")
    ax.axvline(a0, linewidth=0.9, linestyle="--", label=r"cubic slice $a=-1/3$")
    ax.axhline(q0, linewidth=0.8)
    ax.plot([a0], [q0], marker="o", markersize=5, label="Morse critical point")
    ax.set_xlabel(r"$a$")
    ax.set_ylabel(r"$q$")
    ax.set_title(r"Level geometry of $(a;q)_3$ near $(-1/3,-1)$")
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(out_dir / "pochhammer_n3_morse_saddle.png", dpi=220)
    fig.savefig(out_dir / "pochhammer_n3_morse_saddle.pdf")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Gaussian inverse expansions
# ---------------------------------------------------------------------------

def rectangle_partition_coefficients(n: int, k: int, count: int) -> list[int]:
    """Return the first coefficients of [n choose k]_q exactly via SymPy."""
    q = sp.symbols("q")
    # Polynomial recurrence over Z[q].
    row = [sp.Integer(0)] * (k + 1)
    row[0] = sp.Integer(1)
    for nn in range(1, n + 1):
        for kk in range(min(k, nn), 0, -1):
            row[kk] = sp.expand(row[kk] + q ** (nn - kk) * row[kk - 1])
    poly = sp.Poly(row[k], q)
    return [int(poly.nth(j)) for j in range(count)]


def gaussian_inverse_near_zero(n: int, k: int, y: mp.mpf) -> mp.mpf:
    """Cubic inverse jet at q=0 for a nontrivial Gaussian coefficient."""
    coeffs = rectangle_partition_coefficients(n, k, 4)
    c1, c2, c3 = map(mp.mpf, coeffs[1:4])
    u = y - 1
    return u / c1 - c2 * u**2 / c1**3 + (2 * c2**2 - c1 * c3) * u**3 / c1**5


def power_sum_difference(n: int, k: int, power: int) -> mp.mpf:
    """P_r(n,k)=sum_{j=1}^k[(n-k+j)^r-j^r]."""
    return mp.mpf(sum((n - k + j)**power - j**power for j in range(1, k + 1)))


def gaussian_inverse_near_one(n: int, k: int, y: mp.mpf) -> mp.mpf:
    r"""Return the cubic q=e^t inverse jet around q=1.

    Writing s=log(y/binomial(n,k)),
      s=(D/2)t + P_2 t^2/24 + O(t^4).
    There is no t^3 term, by reciprocal symmetry.
    """
    D = mp.mpf(k * (n - k))
    p2 = power_sum_difference(n, k, 2)
    A = D / 2
    B = p2 / 24
    s = mp.log(y / mp.binomial(n, k))
    t = s / A - B * s**2 / A**3 + 2 * B**2 * s**3 / A**5
    return mp.e**t


def gaussian_minus_one_linear_inverse(n: int, k: int, y: mp.mpf) -> mp.mpf:
    """First inverse jet at q=-1, including the cyclotomic-zero case."""
    a, r = divmod(n, 2)
    b, s = divmod(k, 2)
    if r == 0 and s == 1:
        slope = mp.mpf(a - b) * mp.binomial(a, b)
        return -1 + y / slope
    value = mp.binomial(a, b)
    D = mp.mpf(k * (n - k))
    slope = -D * value / 2
    return -1 + (y - value) / slope


def gaussian_inverse_at_infinity(n: int, k: int, y: mp.mpf) -> mp.mpf:
    """Three-term positive large-q inverse from reciprocal symmetry."""
    D = mp.mpf(k * (n - k))
    coeffs = rectangle_partition_coefficients(n, k, 3)
    c2 = mp.mpf(coeffs[2])
    R = y ** (-1 / D)
    return 1 / R - 1 / D + ((D - 1) / (2 * D**2) - c2 / D) * R


def gaussian_validation_rows() -> list[dict[str, str]]:
    """Compare local inverse jets to actual Gaussian coefficient inputs."""
    rows: list[dict[str, str]] = []
    n, k = 8, 3
    tests = [
        ("q=0", mp.mpf("0.015"), lambda y: gaussian_inverse_near_zero(n, k, y)),
        ("q=1", mp.mpf("1.012"), lambda y: gaussian_inverse_near_one(n, k, y)),
        ("q=-1 nonzero", mp.mpf("-0.992"), lambda y: gaussian_minus_one_linear_inverse(n, 2, y)),
        ("q=-1 zero", mp.mpf("-0.992"), lambda y: gaussian_minus_one_linear_inverse(n, 3, y)),
        ("q=infinity", mp.mpf("18"), lambda y: gaussian_inverse_at_infinity(n, k, y)),
    ]
    for name, q_true, inverse in tests:
        kk = 2 if name == "q=-1 nonzero" else k
        y = gaussian_binomial(n, kk, q_true)
        q_approx = inverse(y)
        rows.append({
            "experiment": name,
            "n": str(n),
            "k": str(kk),
            "q_true": mp.nstr(q_true, 30),
            "target_y": mp.nstr(y, 30),
            "q_series": mp.nstr(q_approx, 30),
            "absolute_error": mp.nstr(abs(q_approx - q_true), 12),
        })
    return rows


# ---------------------------------------------------------------------------
# Radial inverse asymptotics at q=1 and q=-1
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class RadialApproximation:
    t_true: mp.mpf
    t_leading: mp.mpf
    t_corrected: mp.mpf
    relerr_leading: mp.mpf
    relerr_corrected: mp.mpf


def radial_inverse_approximation(a: mp.mpf, t: mp.mpf,
                                 root_order: int) -> RadialApproximation:
    r"""Approximate t from y=(a;zeta*exp(-t))_infinity for zeta=1 or -1.

    For zeta=1 (root_order=1):
      log y = -Li_2(a)/t + 1/2 log(1-a) - D t + O(t^3),
      D = a/[12(1-a)].

    For zeta=-1 (root_order=2):
      log y = -Li_2(a^2)/(4t) + 1/2 log(1-a)
              - a(a+3)t/[12(1-a^2)] + O(t^3).

    Reversion of X=A/t+D t+... gives t=A/X+D A^2/X^3+...
    with X=-log(y)+C.  For q=-exp(-t) and real |a|<1, y is real
    and positive, so no logarithmic branch ambiguity is present.
    """
    if root_order == 1:
        q = mp.e**(-t)
        A = mp.polylog(2, a)
        C = mp.log(1 - a) / 2
        D = a / (12 * (1 - a))
    elif root_order == 2:
        q = -mp.e**(-t)
        A = mp.polylog(2, a**2) / 4
        C = mp.log(1 - a) / 2
        D = a * (a + 3) / (12 * (1 - a**2))
    else:
        raise ValueError("implemented roots are 1 and -1")
    log_y = log_qpoch_infinite_lambert(a, q)
    # Imaginary roundoff is absent for these two real rays, but use real part
    # defensively because the Lambert implementation accepts complex inputs.
    X = -mp.re(log_y) + C
    leading = A / X
    corrected = A / X + D * A**2 / X**3
    return RadialApproximation(
        t_true=t,
        t_leading=leading,
        t_corrected=corrected,
        relerr_leading=abs(leading / t - 1),
        relerr_corrected=abs(corrected / t - 1),
    )


def radial_rows_and_figure(out_dir: Path) -> list[dict[str, str]]:
    """Generate radial inversion data and a log-log error plot."""
    a = mp.mpf("0.37")
    t_values = [mp.mpf(str(v)) for v in np.geomspace(0.012, 0.20, 22)]
    rows: list[dict[str, str]] = []

    fig = plt.figure(figsize=(7.2, 4.8))
    ax = fig.add_subplot(111)
    for order, label in [(1, r"$q\to1^-$"), (2, r"$q\to-1$ radially")]:
        approximations = [radial_inverse_approximation(a, t, order) for t in t_values]
        xs = [float(r.t_true) for r in approximations]
        e0 = [float(r.relerr_leading) for r in approximations]
        e1 = [float(r.relerr_corrected) for r in approximations]
        ax.loglog(xs, e0, marker="o", markersize=3, linestyle="--",
                  label=label + " leading")
        ax.loglog(xs, e1, marker="s", markersize=3, linestyle="-",
                  label=label + " corrected")
        for r in approximations:
            rows.append({
                "root": "1" if order == 1 else "-1",
                "a": mp.nstr(a, 12),
                "t_true": mp.nstr(r.t_true, 16),
                "t_leading": mp.nstr(r.t_leading, 20),
                "t_corrected": mp.nstr(r.t_corrected, 20),
                "relative_error_leading": mp.nstr(r.relerr_leading, 12),
                "relative_error_corrected": mp.nstr(r.relerr_corrected, 12),
            })
    ax.set_xlabel(r"radial parameter $t$")
    ax.set_ylabel("relative inverse error")
    ax.set_title(r"Radial inversion of $(a;q)_\infty$, $a=0.37$")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(out_dir / "radial_inverse_errors.png", dpi=220)
    fig.savefig(out_dir / "radial_inverse_errors.pdf")
    plt.close(fig)
    return rows


def primitive_root_constant(a: mp.mpf, m: int, ell: int = 1,
                            terms: int = 10000) -> mp.mpc:
    r"""Constant C_zeta(a) in the radial root-of-unity expansion.

      log(a; zeta*e^{-t})_infinity
        = -Li_2(a^m)/(m^2 t) + C_zeta(a) + O(t).

    The returned branch is continuous from a=0.
    """
    zeta = mp.e ** (2j * mp.pi * ell / m)
    c = mp.log(1 - a**m) / (2 * m)
    for r in range(1, terms + 1):
        if r % m:
            c -= a**r / (r * (1 - zeta**r))
        if a**r < mp.mpf("1e-70"):
            break
    return c


def primitive_root_validation_rows() -> list[dict[str, str]]:
    """Validate the leading + constant expansion at primitive roots m=3,4,5."""
    rows: list[dict[str, str]] = []
    a = mp.mpf("0.29")
    for m in (3, 4, 5):
        zeta = mp.e ** (2j * mp.pi / m)
        A = mp.polylog(2, a**m) / m**2
        C = primitive_root_constant(a, m)
        for t in (mp.mpf("0.08"), mp.mpf("0.05"), mp.mpf("0.03")):
            exact = log_qpoch_infinite_lambert(a, zeta * mp.e**(-t))
            approximation = -A / t + C
            rows.append({
                "m": str(m),
                "t": mp.nstr(t, 12),
                "exact_log_real": mp.nstr(mp.re(exact), 24),
                "exact_log_imag": mp.nstr(mp.im(exact), 24),
                "abs_error_leading_plus_constant": mp.nstr(abs(exact - approximation), 12),
                "error_divided_by_t": mp.nstr(abs(exact - approximation) / t, 12),
            })
    return rows


# ---------------------------------------------------------------------------
# q-gamma at q=0 and q=1
# ---------------------------------------------------------------------------

def make_qgamma_figure(out_dir: Path) -> list[dict[str, str]]:
    """Plot and tabulate the different q->0 regimes of Gamma_q(x)."""
    q_values = np.geomspace(1e-6, 0.18, 180)
    x_values = [mp.mpf("0.4"), mp.mpf("1.5"), mp.mpf("3.0")]
    rows: list[dict[str, str]] = []

    fig = plt.figure(figsize=(7.2, 4.8))
    ax = fig.add_subplot(111)
    for x in x_values:
        vals = [float(log_qgamma(x, mp.mpf(str(q)))) for q in q_values]
        ax.semilogx(q_values, vals, label=rf"$x={mp.nstr(x,3)}$")
        for q in (mp.mpf("1e-5"), mp.mpf("1e-3"), mp.mpf("0.05")):
            exact = log_qgamma(x, q)
            leading = q**x + (x - 2) * q
            rows.append({
                "x": mp.nstr(x, 8),
                "q": mp.nstr(q, 10),
                "log_Gamma_q": mp.nstr(exact, 24),
                "q0_two_term_model": mp.nstr(leading, 24),
                "absolute_error": mp.nstr(abs(exact - leading), 12),
            })
    ax.axhline(0.0, linewidth=0.8)
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"$\log\Gamma_q(x)$")
    ax.set_title(r"Newton-polygon regimes of $\Gamma_q(x)$ near $q=0$")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "qgamma_q0_regimes.png", dpi=220)
    fig.savefig(out_dir / "qgamma_q0_regimes.pdf")
    plt.close(fig)
    return rows


def qgamma_near_one_rows() -> list[dict[str, str]]:
    r"""Validate the second-order expansion of log Gamma_{e^{-t}}(x)."""
    rows: list[dict[str, str]] = []
    for x in map(mp.mpf, ("0.5", "1.5", "3.0", "4.25")):
        A = (x - 1) * (x - 2) / 4
        B = (x - 1) * (x - 2) * (2 * x + 3) / 144
        for t in map(mp.mpf, ("0.05", "0.03", "0.02")):
            q = mp.e**(-t)
            exact = log_qgamma(x, q) - mp.log(mp.gamma(x))
            approximation = -A * t + B * t**2
            rows.append({
                "x": mp.nstr(x, 8),
                "t": mp.nstr(t, 8),
                "exact_log_ratio": mp.nstr(exact, 24),
                "second_order_model": mp.nstr(approximation, 24),
                "absolute_error": mp.nstr(abs(exact - approximation), 12),
                "error_over_t_cubed": mp.nstr(abs(exact - approximation) / t**3, 12),
            })
    return rows


# ---------------------------------------------------------------------------
# Generalized Rvachev/Fabius random series
# ---------------------------------------------------------------------------

def uniform_cumulant(even_order: int) -> mp.mpf:
    """Cumulant of U~Uniform[-1,1] for an even positive order."""
    if even_order <= 0 or even_order % 2:
        raise ValueError("order must be positive and even")
    m = even_order // 2
    return mp.mpf(2) ** (2 * m) * mp.bernpoly(2 * m, 0) / (2 * m)


def atomic_cumulant(q: mp.mpf, even_order: int) -> mp.mpf:
    r"""Cumulant of X_q=(1-q) sum_{j>=0}q^j U_j."""
    return (uniform_cumulant(even_order) * (1 - q) ** even_order /
            (1 - q ** even_order))


def variance_to_q(variance: mp.mpf) -> mp.mpf:
    """Exact inverse q=(1-3V)/(1+3V)."""
    return (1 - 3 * variance) / (1 + 3 * variance)


def make_fabius_figure(out_dir: Path) -> list[dict[str, str]]:
    """Plot the exact variance map and validate cumulant recovery."""
    q_values = np.linspace(0.0, 0.98, 500)
    variances = (1 - q_values) / (3 * (1 + q_values))
    # Relative condition number |d log q / d log V|, avoiding q=0.
    q_cond = q_values[1:]
    v_cond = variances[1:]
    derivative = -6 / (1 + 3 * v_cond) ** 2
    condition = np.abs((v_cond / q_cond) * derivative)

    fig = plt.figure(figsize=(7.2, 4.8))
    ax = fig.add_subplot(111)
    ax.plot(q_values, variances, label=r"$V(q)=(1-q)/(3(1+q))$")
    ax.set_xlabel(r"$q$")
    ax.set_ylabel("variance")
    ax.set_title("Exact parameter observable for the generalized Rvachev law")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "fabius_variance_inverse.png", dpi=220)
    fig.savefig(out_dir / "fabius_variance_inverse.pdf")
    plt.close(fig)

    fig = plt.figure(figsize=(7.2, 4.8))
    ax = fig.add_subplot(111)
    ax.semilogy(q_cond, condition)
    ax.set_xlabel(r"$q$")
    ax.set_ylabel("relative condition number")
    ax.set_title("Conditioning of variance-based recovery")
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "fabius_variance_conditioning.png", dpi=220)
    fig.savefig(out_dir / "fabius_variance_conditioning.pdf")
    plt.close(fig)

    rows: list[dict[str, str]] = []
    for q in map(mp.mpf, ("0.1", "0.25", "0.5", "0.75", "0.93")):
        v = atomic_cumulant(q, 2)
        recovered = variance_to_q(v)
        k4 = atomic_cumulant(q, 4)
        k6 = atomic_cumulant(q, 6)
        rows.append({
            "q": mp.nstr(q, 12),
            "variance": mp.nstr(v, 24),
            "q_from_variance": mp.nstr(recovered, 24),
            "abs_recovery_error": mp.nstr(abs(q - recovered), 12),
            "kappa_4": mp.nstr(k4, 24),
            "kappa_6": mp.nstr(k6, 24),
        })
    return rows


# ---------------------------------------------------------------------------
# Output utilities
# ---------------------------------------------------------------------------

def write_csv(path: Path, rows: Sequence[dict[str, str]]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(rows[0].keys()), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def write_tex_summary(path: Path,
                      minus_rows: Sequence[dict[str, str]],
                      gaussian_rows: Sequence[dict[str, str]],
                      radial_rows: Sequence[dict[str, str]],
                      fabius_rows: Sequence[dict[str, str]]) -> None:
    """Write the exact q=-1 LaTeX table consumed by the report.

    The remaining numerical results are kept in CSV and in the human-readable
    summary.  Keeping this fragment to one tabular environment makes it safe to
    include inside a normal LaTeX table float.
    """
    # Touch representative rows here so an accidental empty experiment group
    # is reported immediately rather than much later during report generation.
    if not gaussian_rows or not radial_rows or not fabius_rows:
        raise ValueError("all numerical experiment groups must be nonempty")

    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write("% Generated by inverse_q_analogs_experiments.py; do not edit.\n")
        f.write("\\begin{tabular}{@{}rrrr@{}}\n")
        f.write("\\toprule\n")
        f.write("$n$ & $a_*$ & critical order & $(a_*;-1)_n$\\\\\n")
        f.write("\\midrule\n")
        for row in minus_rows[:9]:
            f.write(
                f"{row['n']} & ${row['a_star']}$ & "
                f"{row['first_nonzero_derivative_order']} & "
                f"${row['F_minus_one']}$\\\\\n"
            )
        f.write("\\bottomrule\n\\end{tabular}\n")


def write_human_summary(path: Path, groups: dict[str, Sequence[dict[str, str]]]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write("Inverse q-analogs numerical experiment summary\n")
        f.write("================================================\n\n")
        f.write(f"Working precision: {MP_DPS} decimal digits\n\n")
        for name, rows in groups.items():
            f.write(f"{name}: {len(rows)} rows\n")
            if rows:
                for key, value in rows[0].items():
                    f.write(f"  first.{key} = {value}\n")
            f.write("\n")
        f.write("All figures were generated from these calculations.\n")
        f.write("The exact q=-1 table is symbolic over the rationals.\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="experiment root (default: parent of scripts directory)",
    )
    args = parser.parse_args()
    root = args.output.resolve()
    figures = root / "figures"
    data = root / "data"
    output = root / "output"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)

    minus_rows = symbolic_minus_one_table()
    gaussian_rows = gaussian_validation_rows()
    radial_rows = radial_rows_and_figure(figures)
    primitive_rows = primitive_root_validation_rows()
    qgamma0_rows = make_qgamma_figure(figures)
    qgamma1_rows = qgamma_near_one_rows()
    fabius_rows = make_fabius_figure(figures)
    make_minus_one_figure(figures)
    make_n3_morse_figure(figures)

    groups = {
        "finite_pochhammer_minus_one": minus_rows,
        "gaussian_inverse_jets": gaussian_rows,
        "radial_inverse": radial_rows,
        "primitive_root_validation": primitive_rows,
        "qgamma_q0": qgamma0_rows,
        "qgamma_q1": qgamma1_rows,
        "fabius_recovery": fabius_rows,
    }
    for name, rows in groups.items():
        write_csv(data / f"{name}.csv", rows)
    write_tex_summary(output / "numerical_results.tex", minus_rows, gaussian_rows,
                      radial_rows, fabius_rows)
    write_human_summary(output / "numerical_summary.txt", groups)

    print(f"Wrote {sum(len(v) for v in groups.values())} data rows")
    print(f"Figures: {figures}")
    print(f"Tables:  {data}")


if __name__ == "__main__":
    main()
