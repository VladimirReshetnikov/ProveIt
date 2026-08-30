#!/usr/bin/env python3
"""Numerical and symbolic experiments for the inverse q-analogs report.

This script is deliberately self-contained.  It reproduces the numerical
claims and all figures used in the accompanying LaTeX report.  The emphasis is
on branch-aware computations: every real inverse is bracketed on an interval
where monotonicity is proved in the report, and infinite products are evaluated
at elevated precision.

Outputs (created next to this file):
    data/finite_critical_values.csv
    data/infinite_critical_asymptotics.csv
    data/qbinomial_inverse_accuracy.csv
    data/qgamma_minima.csv
    data/principal_inverse_derivative_signs.csv
    data/secondary_discriminants.txt
    figures/finite_pochhammer_collision.pdf
    figures/infinite_critical_asymptotics.pdf
    figures/qbinomial_inverse_accuracy.pdf
    figures/qgamma_inverse_branches.pdf
    figures/principal_inverse.pdf

Dependencies: Python 3.10+, mpmath, sympy, numpy, matplotlib.
No network access is used.
"""

from __future__ import annotations

import csv
import math
from pathlib import Path
from typing import Callable, Iterable, List, Sequence, Tuple

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp

# Keep vector text embedded as TrueType outlines in the archival PDFs.  The
# Matplotlib default (Type 3) is unsuitable for the repository's PDF policy.
plt.rcParams["pdf.fonttype"] = 42
plt.rcParams["ps.fonttype"] = 42

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
FIGURES = ROOT / "figures"
DATA.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)

# High precision is important near coalescing critical values.
mp.mp.dps = 60


def bisect_sign_change(
    f: Callable[[mp.mpf], mp.mpf],
    left: mp.mpf,
    right: mp.mpf,
    *,
    iterations: int = 150,
) -> mp.mpf:
    """Bisection for a continuous function with opposite signs at endpoints."""
    fl = f(left)
    fr = f(right)
    if fl == 0:
        return left
    if fr == 0:
        return right
    if fl * fr > 0:
        raise ValueError(f"No sign change: f(left)={fl}, f(right)={fr}")
    for _ in range(iterations):
        mid = (left + right) / 2
        fm = f(mid)
        if fm == 0:
            return mid
        if fl * fm <= 0:
            right, fr = mid, fm
        else:
            left, fl = mid, fm
    return (left + right) / 2


def bisect_monotone(
    f: Callable[[mp.mpf], mp.mpf],
    target: mp.mpf,
    left: mp.mpf,
    right: mp.mpf,
    *,
    increasing: bool,
    iterations: int = 150,
) -> mp.mpf:
    """Invert a monotone function by bisection on a certified branch."""
    fl, fr = f(left), f(right)
    if increasing:
        if not (fl <= target <= fr):
            raise ValueError((fl, target, fr))
    else:
        if not (fr <= target <= fl):
            raise ValueError((fr, target, fl))
    for _ in range(iterations):
        mid = (left + right) / 2
        fm = f(mid)
        if (fm < target) == increasing:
            left = mid
        else:
            right = mid
    return (left + right) / 2


def qpoch_finite(a: mp.mpf, q: mp.mpf, n: int) -> mp.mpf:
    """Finite q-Pochhammer symbol (a;q)_n."""
    return mp.fprod(1 - a * q**j for j in range(n))


def qpoch_infinite(a: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Infinite q-Pochhammer symbol, delegated to mpmath's q-product."""
    return mp.qp(a, q)


def finite_log_derivative_sum(a: mp.mpf, q: mp.mpf, n: int) -> mp.mpf:
    """S_n(a;q)=sum q^j/(1-aq^j); critical points solve S_n=0."""
    return mp.fsum(q**j / (1 - a * q**j) for j in range(n))


def infinite_log_derivative_sum(a: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Numerical S_infinity(a;q) with a conservative precision cutoff.

    The summands are asymptotic to q^j, so the stopping rule retains a generous
    guard margin relative to the working precision.  This routine supports
    reproducible exploration; rigorous certification should instead combine
    directed rounding with the analytic tail bound proved in the report.
    """
    total = mp.mpf("0")
    j = 0
    cutoff = mp.mpf(10) ** (-(mp.mp.dps - 20))
    while True:
        term = q**j / (1 - a * q**j)
        total += term
        if j > 20 and abs(term) < cutoff:
            break
        j += 1
        if j > 20000:
            raise RuntimeError("Lambert sum did not converge")
    return total


def finite_critical_point(q: mp.mpf, n: int, k: int) -> mp.mpf:
    """Unique critical point in (q^{-k},q^{-(k+1)}), 0<=k<=n-2."""
    left = q ** (-k)
    right = q ** (-(k + 1))
    # Stay away from poles by a relative amount far above mp.eps.
    delta = mp.mpf("1e-35")
    return bisect_sign_change(
        lambda a: finite_log_derivative_sum(a, q, n),
        left + delta * (right - left),
        right - delta * (right - left),
    )


def infinite_critical_point(q: mp.mpf, k: int) -> mp.mpf:
    """Unique critical point of (a;q)_infinity in its k-th zero interval.

    A safeguarded Newton method is much faster than pure bisection because the
    logarithmic derivative is strictly increasing on the interval.
    """
    left_pole = q ** (-k)
    right_pole = q ** (-(k + 1))
    width = right_pole - left_pole
    lo = left_pole + mp.mpf("1e-28") * width
    hi = right_pole - mp.mpf("1e-28") * width
    m = k + 1
    a_asym = q ** (-m) * (1 - mp.mpf(1) / (m + 1))
    # For small m the leading asymptotic can coincide with, or lie beyond, an
    # endpoint (for example q=3/4,m=3).  Start at the midpoint unless the
    # asymptotic estimate is safely inside the interval.
    if lo + mp.mpf("0.08") * width < a_asym < hi - mp.mpf("0.08") * width:
        a = a_asym
    else:
        a = (lo + hi) / 2
    for _ in range(55):
        s = infinite_log_derivative_sum(a, q)
        if s < 0:
            lo = a
        else:
            hi = a
        # S'(a)>0.  Evaluate it with the same conservative truncation.
        spv = mp.mpf(0)
        j = 0
        cutoff = mp.mpf(10) ** (-(mp.mp.dps - 18))
        while True:
            term = q ** (2 * j) / (1 - a * q**j) ** 2
            spv += term
            if j > 20 and abs(term) < cutoff:
                break
            j += 1
        candidate = a - s / spv
        if not (lo < candidate < hi):
            candidate = (lo + hi) / 2
        if abs(candidate - a) <= mp.mpf("1e-45") * max(1, abs(a)):
            return candidate
        a = candidate
    return a


def inverse_qpoch_principal(y: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Principal real inverse A_q(y), defined by (A_q(y);q)_infinity=y."""
    if y <= 0:
        raise ValueError("The principal real branch requires y>0")
    # The function decreases from +infinity at a=-infinity to 0 at a=1.
    right = mp.mpf(1) - mp.mpf("1e-40")
    left = mp.mpf(-1)
    while qpoch_infinite(left, q) < y:
        left *= 2
    return bisect_monotone(
        lambda a: qpoch_infinite(a, q), y, left, right, increasing=False
    )


def qbinomial(n: int, k: int, q: mp.mpf) -> mp.mpf:
    """Gaussian coefficient as a stable finite product."""
    k = min(k, n - k)
    if k < 0:
        return mp.mpf(0)
    if k == 0:
        return mp.mpf(1)
    if abs(q - 1) < mp.mpf("1e-30"):
        return mp.mpf(math.comb(n, k))
    return mp.fprod((1 - q ** (n - k + j)) / (1 - q**j) for j in range(1, k + 1))


def inverse_qbinomial(n: int, k: int, y: mp.mpf) -> mp.mpf:
    """Unique positive q satisfying [n choose k]_q=y, for y>1."""
    if y <= 1 or not (0 < k < n):
        raise ValueError("Need y>1 and 0<k<n")
    classical = mp.mpf(math.comb(n, k))
    if y == classical:
        return mp.mpf(1)
    if y < classical:
        return bisect_monotone(
            lambda q: qbinomial(n, k, q),
            y,
            mp.mpf(0),
            mp.mpf(1),
            increasing=True,
        )
    right = mp.mpf(2)
    while qbinomial(n, k, right) < y:
        right *= 2
    return bisect_monotone(
        lambda q: qbinomial(n, k, q),
        y,
        mp.mpf(1),
        right,
        increasing=True,
    )


def qdigamma(x: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Logarithmic derivative of Gamma_q for 0<q<1."""
    logq = mp.log(q)
    total = mp.mpf("0")
    j = 0
    cutoff = mp.mpf(10) ** (-(mp.mp.dps - 20))
    while True:
        z = q ** (x + j)
        term = z / (1 - z)
        total += term
        if j > 20 and abs(term) < cutoff:
            break
        j += 1
    return -mp.log(1 - q) + logq * total


def qtrigamma(x: mp.mpf, q: mp.mpf) -> mp.mpf:
    """First derivative of q-digamma."""
    logq = mp.log(q)
    total = mp.mpf("0")
    j = 0
    cutoff = mp.mpf(10) ** (-(mp.mp.dps - 20))
    while True:
        z = q ** (x + j)
        term = z / (1 - z) ** 2
        total += term
        if j > 20 and abs(term) < cutoff:
            break
        j += 1
    return logq**2 * total


def qgamma_value(x: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Gamma_q evaluated from logarithmic products (stable for q close to 1)."""
    cutoff = mp.mpf(10) ** (-(mp.mp.dps - 18))
    log_num = mp.mpf(0)
    log_den = mp.mpf(0)
    j = 1
    while True:
        z = q**j
        log_num += mp.log1p(-z)
        if z < cutoff and j > 20:
            break
        j += 1
    j = 0
    while True:
        z = q ** (x + j)
        log_den += mp.log1p(-z)
        if z < cutoff and j > 20:
            break
        j += 1
    return mp.e ** ((1 - x) * mp.log(1 - q) + log_num - log_den)


def qgamma_minimizer(q: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    """Return x_* and Gamma_q(x_*) using safeguarded Newton iteration."""
    lo = mp.mpf("1e-12")
    hi = mp.mpf(6)
    x = mp.mpf("1.45")
    for _ in range(45):
        psi = qdigamma(x, q)
        tri = qtrigamma(x, q)
        if psi < 0:
            lo = x
        else:
            hi = x
        candidate = x - psi / tri
        if not (lo < candidate < hi):
            candidate = (lo + hi) / 2
        if abs(candidate - x) < mp.mpf("1e-42"):
            x = candidate
            break
        x = candidate
    return x, qgamma_value(x, q)

def inverse_qgamma_branches(q: mp.mpf, y: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    """The two positive x-branches solving Gamma_q(x)=y above the minimum."""
    xstar, minimum = qgamma_minimizer(q)
    if y <= minimum:
        raise ValueError("Target must exceed the q-gamma minimum")
    low_left = mp.mpf("1e-30")
    lower = bisect_monotone(
        lambda x: qgamma_value(x, q), y, low_left, xstar, increasing=False
    )
    upper_right = max(mp.mpf(4), 2 * xstar)
    while qgamma_value(upper_right, q) < y:
        upper_right *= 2
    upper = bisect_monotone(
        lambda x: qgamma_value(x, q), y, xstar, upper_right, increasing=True
    )
    return lower, upper


def compose_series(f: Sequence[mp.mpf], g: Sequence[mp.mpf], degree: int) -> List[mp.mpf]:
    """Compose ordinary power series f(g(x)), both having zero constant term."""
    result = [mp.mpf(0)] * (degree + 1)
    power = [mp.mpf(0)] * (degree + 1)
    power[0] = mp.mpf(1)
    for j in range(1, degree + 1):
        # power <- power*g, truncated
        new = [mp.mpf(0)] * (degree + 1)
        for r in range(degree + 1):
            if power[r] == 0:
                continue
            for s in range(1, degree + 1 - r):
                if s < len(g):
                    new[r + s] += power[r] * g[s]
        power = new
        if j < len(f):
            for r in range(degree + 1):
                result[r] += f[j] * power[r]
    return result


def inverse_series_coefficients(f: Sequence[mp.mpf], degree: int) -> List[mp.mpf]:
    """Revert f(x)=f1*x+... numerically, returning g with f(g(x))=x."""
    if len(f) <= degree or f[1] == 0:
        raise ValueError("Need coefficients f[1]...f[degree] with f[1]!=0")
    g = [mp.mpf(0)] * (degree + 1)
    g[1] = 1 / f[1]
    for m in range(2, degree + 1):
        trial = g.copy()
        trial[m] = mp.mpf(0)
        known = compose_series(f, trial, m)[m]
        g[m] = -known / f[1]
    return g


def inverse_derivatives_at_a(q: mp.mpf, a: mp.mpf, degree: int = 8) -> List[mp.mpf]:
    """Derivatives of A_q at y=(a;q)_infinity via Newton sums.

    Writing (a+h;q)_infinity=(a;q)_infinity prod_j(1-h*w_j),
    w_j=q^j/(1-aq^j), gives Taylor coefficients from elementary symmetric
    functions.  Newton's identities avoid numerical differentiation.
    """
    pows = [mp.mpf(0)] * (degree + 1)
    cutoff = mp.mpf(10) ** (-(mp.mp.dps - 18))
    j = 0
    while True:
        w = q**j / (1 - a * q**j)
        for r in range(1, degree + 1):
            pows[r] += w**r
        if j > 20 and abs(w) < cutoff:
            break
        j += 1
    elementary = [mp.mpf(0)] * (degree + 1)
    elementary[0] = mp.mpf(1)
    for r in range(1, degree + 1):
        elementary[r] = mp.fsum(
            (-1) ** (i - 1) * elementary[r - i] * pows[i]
            for i in range(1, r + 1)
        ) / r
    value = qpoch_infinite(a, q)
    f = [mp.mpf(0)] * (degree + 1)
    for r in range(1, degree + 1):
        f[r] = value * (-1) ** r * elementary[r]
    g = inverse_series_coefficients(f, degree)
    return [mp.mpf(0)] + [mp.factorial(j) * g[j] for j in range(1, degree + 1)]

def write_secondary_discriminants() -> Tuple[sp.Expr, mp.mpf]:
    """Compute exact secondary discriminants for n=3,...,6.

    The secondary discriminant is Disc_y Disc_a((a;q)_n-y).  Its non-cyclotomic
    real roots are candidate collisions of distinct critical values.
    """
    q, a, y = sp.symbols("q a y")
    output: List[str] = []
    h5 = None
    for n in range(3, 7):
        p = sp.prod(1 - a * q**j for j in range(n))
        primary = sp.discriminant(p - y, a)
        secondary = sp.factor(sp.discriminant(primary, y))
        output.append(f"n={n}\n{secondary}\n")
        if n == 5:
            # This reciprocal factor is the only one with a root in (0,1).
            h5 = (
                8 * q**10
                - 5 * q**9
                - 7 * q**8
                - 6 * q**7
                - 8 * q**6
                + 35 * q**5
                - 8 * q**4
                - 6 * q**3
                - 7 * q**2
                - 5 * q
                + 8
            )
    assert h5 is not None
    (DATA / "secondary_discriminants.txt").write_text("\n".join(output), encoding="utf-8")
    h5_fun = sp.lambdify(q, h5, "mpmath")
    q0 = bisect_sign_change(h5_fun, mp.mpf("0.8"), mp.mpf("0.9"))
    return h5, q0


def experiment_finite_critical_values(q0: mp.mpf) -> None:
    rows: List[List[str]] = []
    for n in range(3, 11):
        for q in map(mp.mpf, ["0.2", "0.5", "0.8", "0.95"]):
            for k in range(n - 1):
                c = finite_critical_point(q, n, k)
                v = qpoch_finite(c, q, n)
                rows.append([str(n), mp.nstr(q, 18), str(k), mp.nstr(c, 30), mp.nstr(v, 30)])
    # Add high-precision collision data for n=5.
    for k in range(4):
        c = finite_critical_point(q0, 5, k)
        v = qpoch_finite(c, q0, 5)
        rows.append(["5", mp.nstr(q0, 40), str(k), mp.nstr(c, 45), mp.nstr(v, 45)])
    with (DATA / "finite_critical_values.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(["n", "q", "interval_k", "critical_point", "critical_value"])
        writer.writerows(rows)

    # Figure at the first interior Maxwell collision, n=5.
    qf = float(q0)
    critical = [finite_critical_point(q0, 5, k) for k in range(4)]
    a_min = 0.92
    a_max = float(q0 ** (-4)) * 1.04
    aa = np.linspace(a_min, a_max, 2500)
    yy = np.array([float(qpoch_finite(mp.mpf(x), q0, 5)) for x in aa])
    scale = 1e4
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(aa, scale * yy, linewidth=1.5)
    cvs = [qpoch_finite(c, q0, 5) for c in critical]
    ax.scatter([float(c) for c in critical], [scale * float(v) for v in cvs], zorder=3)
    collision_y = (cvs[0] + cvs[2]) / 2
    ax.axhline(scale * float(collision_y), linestyle="--", linewidth=1.0)
    for k, (c, v) in enumerate(zip(critical, cvs)):
        ax.annotate(f"c{k}", (float(c), scale * float(v)), xytext=(4, 6), textcoords="offset points")
    ax.set_xlabel("argument a")
    ax.set_ylabel(r"$10^4\,(a;q)_5$")
    ax.set_title(rf"First critical-value collision for $(a;q)_5$,  $q\approx {qf:.9f}$")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "finite_pochhammer_collision.pdf")
    plt.close(fig)


def experiment_infinite_critical_asymptotics() -> None:
    rows: List[List[str]] = []
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for q in map(mp.mpf, ["0.35", "0.55", "0.75"]):
        ks: List[int] = []
        point_ratios: List[float] = []
        value_ratios: List[float] = []
        qinf = qpoch_infinite(q, q)  # (q;q)_infinity
        for k in range(1, 15):
            m = k + 1
            c = infinite_critical_point(q, k)
            v = abs(qpoch_infinite(c, q))
            c_asym = q ** (-m) * (1 - mp.mpf(1) / (m + 1))
            v_asym = qinf**2 * q ** (-m * (m + 1) / 2) * (mp.mpf(m) ** m) / (mp.mpf(m + 1) ** (m + 1))
            pr = c / c_asym
            vr = v / v_asym
            rows.append([
                mp.nstr(q, 18), str(k), mp.nstr(c, 35), mp.nstr(c_asym, 35),
                mp.nstr(pr, 25), mp.nstr(v, 35), mp.nstr(v_asym, 35), mp.nstr(vr, 25)
            ])
            ks.append(k)
            point_ratios.append(float(pr))
            value_ratios.append(float(vr))
        ax.plot(ks, value_ratios, marker="o", markersize=3, label=rf"$q={float(q):.2f}$")
    with (DATA / "infinite_critical_asymptotics.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "q", "k", "critical_point", "point_asymptotic", "point_ratio",
            "abs_critical_value", "value_asymptotic", "value_ratio"
        ])
        writer.writerows(rows)
    ax.axhline(1.0, linestyle="--", linewidth=1.0)
    ax.set_xlabel("zero interval index k")
    ax.set_ylabel("exact / leading asymptotic for |critical value|")
    ax.set_title("Infinite q-Pochhammer critical-value asymptotics")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "infinite_critical_asymptotics.pdf")
    plt.close(fig)


def experiment_qbinomial_inverse() -> None:
    n, k = 12, 5
    d = k * (n - k)
    classical = mp.mpf(math.comb(n, k))
    rows: List[List[str]] = []
    s_values = [mp.mpf(10) ** (-j / 8) for j in range(4, 33)]
    exact_errors2: List[float] = []
    exact_errors3: List[float] = []
    xs: List[float] = []
    for s in s_values:
        y = classical * mp.e ** (-s)
        q_exact = inverse_qbinomial(n, k, y)
        t_exact = -mp.log(q_exact)
        t1 = 2 * s / d
        t2 = t1 + (n + 1) * s**2 / (3 * d**2)
        t3 = t2 + (n + 1) ** 2 * s**3 / (9 * d**3)
        err2 = abs((t2 - t_exact) / t_exact)
        err3 = abs((t3 - t_exact) / t_exact)
        rows.append([
            mp.nstr(s, 25), mp.nstr(y, 25), mp.nstr(q_exact, 30), mp.nstr(t_exact, 30),
            mp.nstr(t1, 30), mp.nstr(t2, 30), mp.nstr(t3, 30),
            mp.nstr(err2, 20), mp.nstr(err3, 20)
        ])
        xs.append(float(s))
        exact_errors2.append(float(err2))
        exact_errors3.append(float(err3))
    with (DATA / "qbinomial_inverse_accuracy.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "s=-log(y/binomial)", "y", "q_exact", "t_exact=-log(q)",
            "t_linear", "t_quadratic", "t_cubic", "relative_error_quadratic", "relative_error_cubic"
        ])
        writer.writerows(rows)
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.loglog(xs, exact_errors2, marker="o", markersize=3, label="quadratic reversion")
    ax.loglog(xs, exact_errors3, marker="s", markersize=3, label="cubic reversion")
    ax.set_xlabel(r"$s=-\log(y/\binom{12}{5})$")
    ax.set_ylabel("relative error in t=-log q")
    ax.set_title("Near-q=1 inversion of a Gaussian coefficient")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "qbinomial_inverse_accuracy.pdf")
    plt.close(fig)


def experiment_qgamma() -> None:
    rows: List[List[str]] = []
    q_values = list(map(mp.mpf, ["0.05", "0.1", "0.2", "0.4", "0.6", "0.8", "0.95"]))
    for q in q_values:
        xstar, minimum = qgamma_minimizer(q)
        rows.append([mp.nstr(q, 20), mp.nstr(xstar, 35), mp.nstr(minimum, 35), mp.nstr(qtrigamma(xstar, q), 35)])
    with (DATA / "qgamma_minima.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(["q", "x_star", "minimum_Gamma_q", "q_trigamma_at_x_star"])
        writer.writerows(rows)

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    xgrid = np.linspace(0.25, 4.2, 650)
    for qmp in map(mp.mpf, ["0.2", "0.5", "0.8"]):
        q = float(qmp)
        # Vectorized logarithmic-product evaluation for plotting.
        jmax = int(max(80, math.ceil(math.log(1e-15) / math.log(q))))
        js_num = np.arange(1, jmax + 1, dtype=float)
        log_num = np.log1p(-(q ** js_num)).sum()
        vals = []
        for x in xgrid:
            js = np.arange(0, jmax + 1, dtype=float)
            log_den = np.log1p(-(q ** (x + js))).sum()
            vals.append(math.exp((1 - x) * math.log1p(-q) + log_num - log_den))
        ax.plot(xgrid, vals, label=rf"$q={q:.1f}$")
        xstar, minimum = qgamma_minimizer(qmp)
        ax.scatter([float(xstar)], [float(minimum)], s=22)
    ax.set_ylim(0.75, 5.0)
    ax.set_xlabel("x")
    ax.set_ylabel(r"$\Gamma_q(x)$")
    ax.set_title("Two real inverse branches of the q-gamma function")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "qgamma_inverse_branches.pdf")
    plt.close(fig)


def inverse_qpoch_principal_float(y: float, q: float) -> float:
    """Fast double-precision principal inverse for plotting only."""
    logy = math.log(y)
    jmax = int(max(80, math.ceil(math.log(1e-16) / math.log(q))))
    qpow = q ** np.arange(0, jmax + 1, dtype=float)
    def log_product(a: float) -> float:
        return float(np.log1p(-a * qpow).sum())
    right = 1.0 - 1e-14
    left = -1.0
    while log_product(left) < logy:
        left *= 2.0
    for _ in range(75):
        mid = (left + right) / 2.0
        if log_product(mid) > logy:
            left = mid
        else:
            right = mid
    return (left + right) / 2.0


def experiment_principal_inverse() -> None:
    rows: List[List[str]] = []
    for q in map(mp.mpf, ["0.25", "0.5", "0.75"]):
        for a in map(mp.mpf, ["-3", "-1", "0", "0.4", "0.8"]):
            y = qpoch_infinite(a, q)
            derivs = inverse_derivatives_at_a(q, a, 8)
            signs_ok = all(((-1) ** j) * derivs[j] > 0 for j in range(1, 9))
            rows.append([
                mp.nstr(q, 15), mp.nstr(a, 15), mp.nstr(y, 30), str(signs_ok),
                *[mp.nstr(derivs[j], 25) for j in range(1, 9)]
            ])
    with (DATA / "principal_inverse_derivative_signs.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(["q", "a", "y", "alternating_through_order_8"] + [f"A_derivative_{j}" for j in range(1, 9)])
        writer.writerows(rows)

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ygrid = np.logspace(-4, 4, 140)
    for q in map(mp.mpf, ["0.25", "0.5", "0.75"]):
        vals = [inverse_qpoch_principal_float(float(y), float(q)) for y in ygrid]
        ax.semilogx(ygrid, vals, label=rf"$q={float(q):.2f}$")
    ax.axhline(0.0, linewidth=0.8)
    ax.set_xlabel("target y")
    ax.set_ylabel(r"principal inverse $\mathcal{A}_q(y)$")
    ax.set_title("Principal real inverse of the infinite q-Pochhammer product")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "principal_inverse.pdf")
    plt.close(fig)


def write_summary(q0: mp.mpf) -> None:
    c0 = finite_critical_point(q0, 5, 0)
    c2 = finite_critical_point(q0, 5, 2)
    v0 = qpoch_finite(c0, q0, 5)
    v2 = qpoch_finite(c2, q0, 5)
    text = f"""Reproducibility summary
=======================
Working precision: {mp.mp.dps} decimal digits

First interior critical-value collision for n=5:
q0 = {mp.nstr(q0, 70)}
c0 = {mp.nstr(c0, 70)}
c2 = {mp.nstr(c2, 70)}
P_5(c0;q0) = {mp.nstr(v0, 70)}
P_5(c2;q0) = {mp.nstr(v2, 70)}
difference = {mp.nstr(v0-v2, 30)}

All data files and figures were generated by numerical_experiments.py.
"""
    (DATA / "summary.txt").write_text(text, encoding="utf-8")


def main() -> None:
    _, q0 = write_secondary_discriminants()
    experiment_finite_critical_values(q0)
    experiment_infinite_critical_asymptotics()
    experiment_qbinomial_inverse()
    experiment_qgamma()
    experiment_principal_inverse()
    write_summary(q0)
    print(f"Generated data and figures under {ROOT}")
    print(f"n=5 collision q0 = {mp.nstr(q0, 50)}")


if __name__ == "__main__":
    main()
