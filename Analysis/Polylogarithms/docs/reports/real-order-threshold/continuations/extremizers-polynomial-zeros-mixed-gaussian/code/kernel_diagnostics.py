#!/usr/bin/env python3
"""Reproduce Section 2's kernel diagnostics, symbolic replay, and figure.

Dependencies: mpmath, NumPy, Matplotlib; SymPy unless --skip-symbolic is used.
The numerical runs locate interior stationary points by continuation and check
their local Hessians at high precision.  They are NOT finite-N global maximum
certificates.  The limit and eventual global identification follow from the
article.  Exact interval enclosures are separately replayed by verify_kernel.py.

Run ``python code/kernel_diagnostics.py`` from any working directory.  It writes
data/kernel_diagnostics.json and figures/kernel_asymptotics.{pdf,png}.  The
symbolic subresultant checks are exact SymPy arithmetic, separately labeled in
the JSON; the displayed derivative constants and stationary values are ordinary
high-precision diagnostics.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import time

import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


BASE = Path(__file__).resolve().parents[1]
DEFAULT_INDICES = [2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32, 48, 64,
                   96, 128, 192, 256, 384, 512, 768, 1024]


def number(x):
    return mp.nstr(x, 75)


def derivative(f, x, orders):
    return mp.diff(f, (x[0], x[1]), orders)


def gradient(f, x):
    return mp.matrix([derivative(f, x, (1, 0)),
                      derivative(f, x, (0, 1))])


def hessian(f, x):
    mixed = derivative(f, x, (1, 1))
    return mp.matrix([[derivative(f, x, (2, 0)), mixed],
                      [mixed, derivative(f, x, (0, 2))]])


def limiting_constants():
    def q(y):
        return 1 + y - y*y - y**3 + 4*y*mp.log(y)

    y = mp.findroot(q, (mp.mpf("0.14"), mp.mpf("0.15")))
    c = (1 + y) / (2 * y)
    x = mp.matrix([c, y])

    def h0(c, y):
        return (mp.exp(-c*y*y) - mp.exp(-c)) / (1-y)

    def p1(v):
        return -v - v*v/2

    def p2(v):
        return v*v + v**3/6 + v**4/8

    def h1(c, y):
        return (mp.exp(-c*y*y)*p1(c*y*y) - mp.exp(-c)*p1(c))/(1-y)

    def h2(c, y):
        return (mp.exp(-c*y*y)*p2(c*y*y) - mp.exp(-c)*p2(c))/(1-y)

    j = hessian(h0, x)
    q1 = gradient(h1, x)
    x1 = -mp.lu_solve(j, q1)
    minf = h0(c, y)
    mu1 = minf * c*c * y*y / 2
    if abs(mu1-h1(c, y)) > mp.mpf("1e-75"):
        raise ArithmeticError("Two formulas for the first correction disagree")
    mu2 = h2(c, y) - (q1.T * mp.lu_solve(j, q1))[0] / 2
    if not (j[0, 0] < 0 and mp.det(j) > 0):
        raise ArithmeticError("The limiting Hessian failed the numerical check")
    return {
        "y_inf": y, "c_inf": c, "M_inf": minf,
        "mu1": mu1, "mu2": mu2, "x1_c": x1[0], "x1_y": x1[1],
        "Hessian_cc": j[0, 0], "Hessian_cy": j[0, 1],
        "Hessian_yy": j[1, 1], "Hessian_determinant": mp.det(j),
    }


def kernel_scaled(n):
    def f(v):
        return mp.exp(n * mp.log1p(-v/n) - mp.log1p(v/n))

    def kernel(c, y):
        return (f(c*y*y)-f(c))/(1-y)

    return kernel


def stationary_diagnostics(constants, indices):
    # The first seed is safely inside the exact N=2 solution's bracket region.
    previous = (mp.mpf("1.70451695406"), mp.mpf("0.25270267837"))
    rows = []
    for n in indices:
        kernel = kernel_scaled(n)

        def gc(c, y):
            return mp.diff(kernel, (c, y), (1, 0))

        def gy(c, y):
            return mp.diff(kernel, (c, y), (0, 1))

        x = mp.findroot((gc, gy), previous,
                        tol=mp.mpf("1e-75"), maxsteps=60)
        c, y = x[0], x[1]
        if not (0 < c < n and 0 < y < 1):
            raise ArithmeticError(f"N={n}: stationary point outside the domain")
        grad = gradient(kernel, x)
        residual = max(abs(grad[0]), abs(grad[1]))
        j = hessian(kernel, x)
        if residual > mp.mpf("1e-65"):
            raise ArithmeticError(f"N={n}: stationary residual is too large")
        if not (j[0, 0] < 0 and mp.det(j) > 0):
            raise ArithmeticError(f"N={n}: Hessian is not negative definite")
        value = kernel(c, y)
        scaled_excess = n * (value - constants["M_inf"])
        approximation = constants["mu1"] + constants["mu2"]/n
        rows.append({
            "N": n,
            "status": "high-precision interior stationary value; diagnostic",
            "c_stationary": number(c),
            "p_stationary": number(c/n),
            "y_stationary": number(y),
            "M_stationary": number(value),
            "N_times_stationary_excess": number(scaled_excess),
            "mu1_plus_mu2_over_N": number(approximation),
            "scaled_expansion_difference": number(scaled_excess-approximation),
            "gradient_max_abs": number(residual),
            "Hessian_cc": number(j[0, 0]),
            "Hessian_determinant": number(mp.det(j)),
        })
        previous = (c, y)
    return rows


def symbolic_checks():
    import sympy as sp

    p, y = sp.symbols("p y")
    f2 = lambda v: (1-v)**2/(1+v)
    quotient = (f2(p*y*y)-f2(p))/(1-y)
    simple = p*(1+y)*(4/((1+p)*(1+p*y*y))-1)
    if sp.factor(quotient-simple) != 0:
        raise ArithmeticError("The exact rational N=2 kernel identity failed")
    p_actual = sp.factor(sp.together(sp.diff(simple, p)/(1+y))).as_numer_denom()[0]
    q_actual = sp.factor(sp.together(sp.diff(simple, y)/p)).as_numer_denom()[0]
    p_expected = (-p**4*y**4-2*p**3*y**4-2*p**3*y**2-p**2*y**4
                  -8*p**2*y**2-p**2-2*p*y**2-2*p+3)
    q_expected = (-p**3*y**4-p**2*y**4-2*p**2*y**2-6*p*y**2
                  -8*p*y-p+3)
    if sp.expand(p_actual-p_expected) != 0:
        raise ArithmeticError("The first exact gradient numerator failed")
    if sp.expand(q_actual-q_expected) != 0:
        raise ArithmeticError("The second exact gradient numerator failed")
    d = y**6+2*y**5-2*y**4-6*y**3+17*y**2+36*y+4
    g = y**7+3*y**6-2*y**5-10*y**4+17*y**3+59*y**2-4
    subresultants = sp.subresultants(p_actual, q_actual, p)
    expected_last_two = [-16*y**10*(p*d-12), 192*y**10*(y+1)*g]
    for actual, expected in zip(subresultants[-2:], expected_last_two):
        if sp.expand(actual-expected) != 0:
            raise ArithmeticError("An exact subresultant identity failed")
    return {
        "status": "exact symbolic arithmetic, distinct from numerical diagnostics",
        "sympy_version": sp.__version__,
        "rational_kernel_identity": "passed",
        "gradient_numerators": "both passed",
        "penultimate_subresultant": str(sp.factor(subresultants[-2])),
        "last_subresultant": str(sp.factor(subresultants[-1])),
        "both_subresultant_identities": "passed",
    }


def check_certificate_agreement(constants, rows):
    """Compare diagnostic numbers with independently generated rational bounds.

    Passing this comparison does not turn the diagnostic into an interval proof.
    It detects inconsistent normalization or transcription between the layers.
    """
    certificate_path = BASE / "data" / "kernel_certificate.json"
    if not certificate_path.exists():
        raise FileNotFoundError("First run verify_kernel.py --write")
    from fractions import Fraction
    enclosures = json.loads(certificate_path.read_text())["certified_intervals"]
    values = {name: constants[name] for name in ("y_inf", "c_inf", "M_inf", "mu1")}
    first = next((row for row in rows if row["N"] == 2), None)
    if first is not None:
        values.update(y2=mp.mpf(first["y_stationary"]),
                      p2=mp.mpf(first["p_stationary"]),
                      M2=mp.mpf(first["M_stationary"]))
    for name, value in values.items():
        lower_fraction = Fraction(enclosures[name]["lower"])
        upper_fraction = Fraction(enclosures[name]["upper"])
        lower = mp.mpf(lower_fraction.numerator)/lower_fraction.denominator
        upper = mp.mpf(upper_fraction.numerator)/upper_fraction.denominator
        if not lower <= value <= upper:
            raise ArithmeticError(f"Diagnostic {name} misses the rational enclosure")
    return sorted(values)


def make_figure(constants, rows):
    figure_dir = BASE / "figures"
    figure_dir.mkdir(parents=True, exist_ok=True)
    n_values = np.array([row["N"] for row in rows], dtype=float)
    scaled = np.array([float(row["N_times_stationary_excess"]) for row in rows])
    n_curve = np.geomspace(n_values.min(), n_values.max(), 500)
    mu1 = float(constants["mu1"])
    mu2 = float(constants["mu2"])
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "pdf.fonttype": 42, "ps.fonttype": 42,
    })
    fig, ax = plt.subplots(figsize=(8.2, 4.9), layout="constrained")
    ax.plot(n_values, scaled, "o-", color="#185b81", markersize=4.5,
            linewidth=1.4, label="Local stationary values (diagnostic)")
    ax.plot(n_curve, mu1+mu2/n_curve, color="#be6636", linewidth=1.8,
            label=r"$\mu_1+\mu_2/N$")
    ax.axhline(mu1, color="#596571", linewidth=1.2, linestyle="--",
               label=r"$\mu_1$")
    ax.set_xscale("log")
    ax.set_xlim(1.8, 1200)
    ax.set_ylim(0, 0.185)
    ax.set_xlabel(r"Truncation index $N$")
    ax.set_ylabel(r"$N(\widetilde M_N-M_\infty)$")
    ax.set_title("Euler kernel extrema: convergence of the scaled excess",
                 loc="left", fontweight="bold", pad=13)
    ax.grid(axis="both", color="#dfe5e8", linewidth=0.6)
    ax.set_axisbelow(True)
    ax.legend(loc="lower right", frameon=True, facecolor="white",
              edgecolor="#dfe5e8", fontsize=9)
    fig.supxlabel(
        r"$\widetilde M_N$ denotes a numerically located interior stationary value. "
        "Global conclusions use the article's proofs.",
        fontsize=8, color="#4d5963")
    for extension in ("pdf", "png"):
        output = figure_dir / f"kernel_asymptotics.{extension}"
        fig.savefig(output, dpi=200, metadata={"Creator": "kernel_diagnostics.py"})
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-symbolic", action="store_true",
                        help="Omit the exact SymPy replay")
    args = parser.parse_args()
    start = time.perf_counter()
    mp.mp.dps = 95
    constants = limiting_constants()
    rows = stationary_diagnostics(constants, DEFAULT_INDICES)
    agreements = check_certificate_agreement(constants, rows)
    symbolic = ({"status": "not run; --skip-symbolic was requested"}
                if args.skip_symbolic else symbolic_checks())
    make_figure(constants, rows)
    output = {
        "schema_version": 1,
        "scope": (
            "Numerical stationary points, local Hessian checks, and asymptotic "
            "coefficient diagnostics. No finite-N global search certificate. "
            "The exact SymPy checks below have their own narrower algebraic scope."
        ),
        "working_decimal_precision": mp.mp.dps,
        "software_versions": {
            "mpmath": mp.__version__, "numpy": np.__version__,
            "matplotlib": matplotlib.__version__,
        },
        "method": (
            "High-precision two-variable stationary equations, continued from "
            "the exact N=2 solution along the listed indices; no exhaustive scan."
        ),
        "constants": {name: number(value) for name, value in constants.items()},
        "agreement_with_rational_certificate": agreements,
        "exact_symbolic_checks": symbolic,
        "stationary_diagnostics": rows,
        "figure": "figures/kernel_asymptotics.pdf",
    }
    data_dir = BASE / "data"
    data_dir.mkdir(parents=True, exist_ok=True)
    (data_dir / "kernel_diagnostics.json").write_text(json.dumps(output, indent=2)+"\n")
    for name in ("y_inf", "c_inf", "M_inf", "mu1", "mu2", "x1_c", "x1_y"):
        print(f"{name} = {number(constants[name])}")
    print(f"Reproduced {len(rows)} diagnostic stationary points.")
    print("Exact SymPy replay:", symbolic["status"])
    print("Wrote kernel_diagnostics.json and kernel_asymptotics.pdf/.png.")
    print(f"Elapsed: {time.perf_counter()-start:.3f} seconds")


if __name__ == "__main__":
    main()
