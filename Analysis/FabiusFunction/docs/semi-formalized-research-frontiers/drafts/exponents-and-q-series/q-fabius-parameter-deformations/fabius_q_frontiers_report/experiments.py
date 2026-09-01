#!/usr/bin/env python3
"""Reproducible numerical experiments for the q-Fabius frontier report.

The report studies the centered geometric-uniform random series

    X_q = (1-q) * sum_{j>=0} q**j U_j,       U_j ~ Uniform[-1,1],

and its standardized version Z_q = X_q/sigma_q.  At q=1/2 this is the
centered Rvachev up-law (equivalently, an affine form of the Fabius law).

This script performs four independent checks:

1. Midpoint Euler--Maclaurin expansion of the scaled cumulant generating
   function as q -> 1.
2. The limiting large-deviation rate function, its central Taylor series,
   and the Lambert-W_{-1} endpoint approximation.
3. Fourier inversion of the standardized infinite sinc product and the
   predicted all-order Edgeworth error hierarchy.
4. A Monte-Carlo stop-loss diagnostic for the exact convex-order parameter
   flow X_s <=_cx X_r when 0 < r < s < 1.

Outputs are written under data/ and figures/.  Both PNG and vector PDF plots
are produced.  The calculations are deterministic apart from experiment 4,
which uses the fixed seed below.

Dependencies: Python >=3.10, numpy, scipy, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, simpson
from scipy.special import eval_hermitenorm, lambertw
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
FIGURES = ROOT / "figures"
DATA.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)

# Endpoint constant in Lambda(theta) = theta - .5 log(theta)^2
# - log(2) log(theta) + C_LAMBDA + o(1).  It is independently recomputed
# in compute_endpoint_constant().
C_LAMBDA_REFERENCE = -0.9689204239630313182711571541836242862827791946101951


def save_figure(fig: plt.Figure, stem: str) -> None:
    """Save a figure in both portable raster and vector formats."""
    fig.tight_layout()
    fig.savefig(FIGURES / f"{stem}.png", dpi=220, bbox_inches="tight")
    fig.savefig(FIGURES / f"{stem}.pdf", bbox_inches="tight")
    plt.close(fig)


def sinhc_log(x: np.ndarray | float) -> np.ndarray | float:
    """Return log(sinh(x)/x), stably near zero, for real x.

    The function is even.  The Taylor branch avoids 0/0 and cancellation.
    For the parameter ranges in this script |x| is moderate, so overflow is
    not an issue.
    """
    a = np.asarray(x, dtype=float)
    aa = np.abs(a)
    out = np.empty_like(aa)
    small = aa < 1.0e-4
    z = aa[small]
    z2 = z * z
    out[small] = (
        z2 / 6.0
        - z2**2 / 180.0
        + z2**3 / 2835.0
        - z2**4 / 37800.0
        + z2**5 / 467775.0
    )
    z = aa[~small]
    out[~small] = np.log(np.sinh(z) / z)
    if np.isscalar(x):
        return float(out)
    return out


def lambda_limit(theta: float) -> float:
    """Limiting scaled CGF Lambda(theta) by adaptive quadrature."""
    if theta == 0.0:
        return 0.0
    t = abs(theta)

    def integrand(u: float) -> float:
        return float(sinhc_log(u)) / u if u else 0.0

    # Lambda is even.  Splitting at 1 helps the adaptive quadrature for large t.
    if t <= 1.0:
        val, _ = quad(integrand, 0.0, t, epsabs=2e-13, epsrel=2e-13, limit=200)
    else:
        val1, _ = quad(integrand, 0.0, 1.0, epsabs=2e-13, epsrel=2e-13, limit=200)
        val2, _ = quad(integrand, 1.0, t, epsabs=2e-13, epsrel=2e-13, limit=400)
        val = val1 + val2
    # The sign disappears because the integral of the odd integrand from 0
    # to a negative endpoint is positive.
    return float(val)


def lambda_prime(theta: np.ndarray | float) -> np.ndarray | float:
    """Lambda'(theta) = log(sinh(theta)/theta)/theta, with its value at 0."""
    a = np.asarray(theta, dtype=float)
    out = np.empty_like(a)
    small = np.abs(a) < 1.0e-5
    z = a[small]
    out[small] = z / 6.0 - z**3 / 180.0 + z**5 / 2835.0 - z**7 / 37800.0
    out[~small] = sinhc_log(a[~small]) / a[~small]
    if np.isscalar(theta):
        return float(out)
    return out


def lambda_second(theta: np.ndarray | float) -> np.ndarray | float:
    """Strictly positive second derivative of the limiting scaled CGF."""
    a = np.asarray(theta, dtype=float)
    out = np.empty_like(a)
    small = np.abs(a) < 1.0e-4
    z = a[small]
    out[small] = 1.0 / 6.0 - z**2 / 60.0 + z**4 / 567.0 - z**6 / 5400.0
    z = a[~small]
    out[~small] = (z / np.tanh(z) - sinhc_log(z) - 1.0) / z**2
    if np.isscalar(theta):
        return float(out)
    return out


def lambda_finite(delta: float, theta: float, cutoff: float = 1.0e-12) -> float:
    """Exact scaled CGF for q=exp(-delta), evaluated by its midpoint sum.

    The exact identity is

      delta log E exp(theta X_q/delta)
        = delta sum_{j>=0} g(theta*s_delta*exp(-(j+1/2)delta)),

    where g=log(sinhc) and s_delta=2sinh(delta/2)/delta.  The omitted tail is
    bounded by a geometric multiple of its first term because g(z)=O(z^2).
    """
    s_delta = 2.0 * math.sinh(delta / 2.0) / delta
    if theta == 0.0:
        return 0.0
    # Choose J so the first omitted argument is tiny.  Since the tail is
    # quadratic, cutoff in the argument gives roughly cutoff^2 accuracy.
    j_max = max(
        1,
        int(math.ceil((math.log(abs(theta) * s_delta / cutoff) / delta) - 0.5)),
    )
    j = np.arange(j_max, dtype=float)
    args = theta * s_delta * np.exp(-(j + 0.5) * delta)
    main = delta * float(np.sum(sinhc_log(args)))

    # Add the leading analytic tail sum g(z)=z^2/6+O(z^4).  This makes the
    # truncation error far smaller than the plotted Euler--Maclaurin errors.
    first = theta * s_delta * math.exp(-(j_max + 0.5) * delta)
    tail2 = delta * first * first / (6.0 * (1.0 - math.exp(-2.0 * delta)))
    return main + tail2


def compute_endpoint_constant() -> float:
    """Compute the convergent integral defining the endpoint constant."""

    def a_integrand(u: float) -> float:
        return float(sinhc_log(u)) / u if u else 0.0

    def b_integrand(u: float) -> float:
        return math.log1p(-math.exp(-2.0 * u)) / u

    a, _ = quad(a_integrand, 0.0, 1.0, epsabs=2e-13, epsrel=2e-13, limit=300)
    b, _ = quad(b_integrand, 1.0, np.inf, epsabs=2e-13, epsrel=2e-13, limit=300)
    return a - 1.0 + b


def experiment_cgf(quick: bool) -> dict[str, float]:
    """Check the O(delta^2) and corrected O(delta^4) CGF laws."""
    deltas = np.array([0.40, 0.30, 0.22, 0.16, 0.12, 0.09, 0.065, 0.045])
    if quick:
        deltas = deltas[::2]
    thetas = np.array([0.5, 1.0, 2.0, 4.0])

    rows: list[dict[str, float]] = []
    max_raw: list[float] = []
    max_corrected: list[float] = []
    for delta in deltas:
        raw_errors = []
        corrected_errors = []
        for theta in thetas:
            exact = lambda_finite(float(delta), float(theta))
            limit = lambda_limit(float(theta))
            correction = -delta**2 * theta**2 * lambda_second(theta) / 24.0
            corrected = limit + correction
            raw = abs(exact - limit)
            corr = abs(exact - corrected)
            raw_errors.append(raw)
            corrected_errors.append(corr)
            rows.append(
                {
                    "delta": float(delta),
                    "q": math.exp(-float(delta)),
                    "theta": float(theta),
                    "lambda_q": exact,
                    "lambda_limit": limit,
                    "raw_error": raw,
                    "corrected_error": corr,
                }
            )
        max_raw.append(max(raw_errors))
        max_corrected.append(max(corrected_errors))

    with (DATA / "cgf_midpoint_convergence.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    # Fit slopes on the smallest four deltas (all available in quick mode).
    fit_n = min(4, len(deltas))
    slope_raw = float(np.polyfit(np.log(deltas[-fit_n:]), np.log(max_raw[-fit_n:]), 1)[0])
    slope_corr = float(
        np.polyfit(np.log(deltas[-fit_n:]), np.log(max_corrected[-fit_n:]), 1)[0]
    )

    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.loglog(deltas, max_raw, "o-", label="uncorrected")
    ax.loglog(deltas, max_corrected, "s-", label="after $\\delta^2$ correction")
    reference = max_raw[-1] * (deltas / deltas[-1]) ** 2
    ax.loglog(deltas, reference, "--", label="slope 2 reference")
    reference4 = max_corrected[-1] * (deltas / deltas[-1]) ** 4
    ax.loglog(deltas, reference4, ":", label="slope 4 reference")
    ax.set_xlabel(r"$\delta=-\log q$")
    ax.set_ylabel("maximum absolute CGF error")
    ax.set_title("Midpoint Euler--Maclaurin cancellation")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    save_figure(fig, "cgf_midpoint_correction")
    return {"cgf_raw_slope": slope_raw, "cgf_corrected_slope": slope_corr}


def rate_center_series(x: np.ndarray) -> np.ndarray:
    """Rate-function Taylor polynomial through x^14."""
    return (
        3.0 * x**2
        + 9.0 / 5.0 * x**4
        + 276.0 / 175.0 * x**6
        + 1188.0 / 875.0 * x**8
        + 354672.0 / 336875.0 * x**10
        + 1507248.0 / 1990625.0 * x**12
        + 496585728.0 / 766390625.0 * x**14
    )


def experiment_rate_function(quick: bool) -> dict[str, float]:
    """Construct the rate function parametrically and test Lambert endpoint law."""
    c_lambda = compute_endpoint_constant()

    # A mixed grid resolves both the center and the x -> 1 boundary.
    theta_grid = np.unique(
        np.concatenate(
        [
            np.linspace(0.0, 2.0, 160 if not quick else 80),
            np.geomspace(2.01, 250.0, 260 if not quick else 120),
        ]
    ))
    x_grid = lambda_prime(theta_grid)
    lambda_grid = np.array([lambda_limit(float(t)) for t in theta_grid])
    rate = theta_grid * x_grid - lambda_grid
    center = rate_center_series(x_grid)

    eta = 1.0 - x_grid
    lambert_rate = np.full_like(rate, np.nan)
    theta_lambert = np.full_like(rate, np.nan)
    mask = (eta > 0.0) & (eta < 0.20)
    w = lambertw(-eta[mask] / 2.0, k=-1).real
    theta_lambert[mask] = -w / eta[mask]
    log_theta = np.log(theta_lambert[mask])
    lambert_rate[mask] = (
        0.5 * log_theta**2
        + (math.log(2.0) - 1.0) * log_theta
        - math.log(2.0)
        - c_lambda
    )

    rows = []
    for t, xx, rr, cc, lr, tl in zip(
        theta_grid, x_grid, rate, center, lambert_rate, theta_lambert
    ):
        rows.append(
            {
                "theta": float(t),
                "x": float(xx),
                "rate": float(rr),
                "center_series": float(cc),
                "lambert_rate": float(lr) if np.isfinite(lr) else "",
                "lambert_theta": float(tl) if np.isfinite(tl) else "",
            }
        )
    with (DATA / "large_deviation_rate.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.plot(x_grid, rate, label="exact parametric rate")
    center_mask = x_grid <= 0.68
    ax.plot(x_grid[center_mask], center[center_mask], "--", label="center series through $x^{14}$")
    endpoint_mask = np.isfinite(lambert_rate) & (x_grid >= 0.80)
    ax.plot(x_grid[endpoint_mask], lambert_rate[endpoint_mask], ":", label="Lambert-$W_{-1}$ endpoint law")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$I(x)$")
    ax.set_title("Large-deviation rate function for the geometric-uniform family")
    ax.set_xlim(0.0, 0.997)
    ax.set_ylim(bottom=0.0)
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, "rate_function_lambert")

    endpoint_error = np.nanmax(
        np.abs(rate[endpoint_mask] - lambert_rate[endpoint_mask])
        / np.maximum(1.0, rate[endpoint_mask])
    )
    return {
        "endpoint_constant": c_lambda,
        "endpoint_constant_reference_error": abs(c_lambda - C_LAMBDA_REFERENCE),
        "lambert_max_relative_error_x_ge_0_8": float(endpoint_error),
    }


def standardized_cumulants(q: float) -> tuple[float, float, float]:
    """Return lambda_4, lambda_6, lambda_8 of Z_q exactly in q."""
    l4 = -6.0 * (1.0 - q * q) / (5.0 * (1.0 + q * q))
    l6 = 48.0 * (1.0 - q * q) ** 2 / (7.0 * (1.0 + q * q + q**4))
    l8 = -432.0 * (1.0 - q * q) ** 3 / (
        5.0 * (1.0 + q * q) * (1.0 + q**4)
    )
    return l4, l6, l8


def edgeworth_density(q: float, x: np.ndarray, order: int) -> np.ndarray:
    """Exact-cumulant Edgeworth approximation of weighted order 0..3."""
    phi = np.exp(-x * x / 2.0) / math.sqrt(2.0 * math.pi)
    if order == 0:
        return phi
    l4, l6, l8 = standardized_cumulants(q)
    poly = np.ones_like(x)
    poly += l4 / math.factorial(4) * eval_hermitenorm(4, x)
    if order >= 2:
        poly += l6 / math.factorial(6) * eval_hermitenorm(6, x)
        poly += l4**2 / (2.0 * math.factorial(4) ** 2) * eval_hermitenorm(8, x)
    if order >= 3:
        poly += l8 / math.factorial(8) * eval_hermitenorm(8, x)
        poly += l4 * l6 / (math.factorial(4) * math.factorial(6)) * eval_hermitenorm(10, x)
        poly += l4**3 / (6.0 * math.factorial(4) ** 3) * eval_hermitenorm(12, x)
    return phi * poly


def standardized_characteristic(q: float, t: np.ndarray, arg_tol: float = 1e-10) -> tuple[np.ndarray, int]:
    """Evaluate the infinite sinc product of Z_q by a controlled truncation.

    If b=sqrt(3(1-q^2)), then chi_q(t)=prod_j sinc(b q^j t).  We retain factors
    until the largest omitted argument is below arg_tol.  The omitted logarithm
    is approximately -q^(2J)t^2/2 and is negligible at the chosen tolerance.
    """
    b = math.sqrt(3.0 * (1.0 - q * q))
    t_max = float(np.max(np.abs(t)))
    if q == 0.0:
        return np.sinc(b * t / math.pi), 1
    j_max = max(1, int(math.ceil(math.log(arg_tol / (b * t_max)) / math.log(q))))
    product = np.ones_like(t)
    q_power = 1.0
    for _ in range(j_max):
        product *= np.sinc((b * q_power * t) / math.pi)
        q_power *= q
    # Incorporate the quadratic tail rather than simply dropping it.
    product *= np.exp(-0.5 * q_power**2 * t**2)
    return product, j_max


def standardized_density_fourier(
    q: float, x: np.ndarray, *, t_max: float, n_t: int
) -> tuple[np.ndarray, int, float]:
    """Invert the even characteristic function by a cosine transform."""
    t = np.linspace(0.0, t_max, n_t)
    chi, n_factors = standardized_characteristic(q, t)
    density = np.empty_like(x)
    # Chunking prevents a large x-by-t cosine matrix from dominating memory.
    for start in range(0, x.size, 48):
        xx = x[start : start + 48]
        integrand = np.cos(np.outer(xx, t)) * chi
        density[start : start + xx.size] = simpson(integrand, x=t, axis=1) / math.pi
    return density, n_factors, float(abs(chi[-1]))


def experiment_edgeworth(quick: bool) -> dict[str, float]:
    """Numerically verify the O((1-q)^(R+1)) Edgeworth hierarchy."""
    q_values = np.array([0.82, 0.86, 0.90, 0.93, 0.95, 0.965, 0.975])
    if quick:
        q_values = q_values[::2]
    x = np.linspace(-5.5, 5.5, 321 if not quick else 201)
    t_max = 30.0
    n_t = 24001 if not quick else 12001

    rows = []
    errors: dict[int, list[float]] = {r: [] for r in range(4)}
    for q in q_values:
        density, n_factors, tail_value = standardized_density_fourier(
            float(q), x, t_max=t_max, n_t=n_t
        )
        for order in range(4):
            approximation = edgeworth_density(float(q), x, order)
            sup_error = float(np.max(np.abs(density - approximation)))
            errors[order].append(sup_error)
            rows.append(
                {
                    "q": float(q),
                    "delta": float(-math.log(q)),
                    "epsilon": float(1.0 - q),
                    "order": order,
                    "sup_error": sup_error,
                    "sinc_factors": n_factors,
                    "abs_cf_at_tmax": tail_value,
                }
            )
    with (DATA / "edgeworth_errors.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    delta_values = -np.log(q_values)
    slopes: dict[str, float] = {}
    fit_n = min(4, len(q_values))
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for order in range(4):
        err = np.array(errors[order])
        slope = float(np.polyfit(np.log(delta_values[-fit_n:]), np.log(err[-fit_n:]), 1)[0])
        slopes[f"edgeworth_order_{order}_slope"] = slope
        ax.loglog(delta_values, err, "o-", label=f"weighted order {order}; fit {slope:.2f}")
    ax.set_xlabel(r"$\delta=-\log q$")
    ax.set_ylabel(r"$L^\infty$ density error")
    ax.set_title("Continuous-parameter Edgeworth hierarchy")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    save_figure(fig, "edgeworth_errors")
    return slopes


def empirical_stop_loss(sorted_samples: np.ndarray, thresholds: np.ndarray) -> np.ndarray:
    """Compute empirical E[(X-t)_+] from a sorted sample in O(n+m log n)."""
    n = sorted_samples.size
    # Use a transparent suffix array of length n+1, including the
    # empty suffix at the right endpoint.
    suffix = np.zeros(n + 1)
    suffix[:-1] = np.cumsum(sorted_samples[::-1])[::-1]
    idx = np.searchsorted(sorted_samples, thresholds, side="right")
    counts = n - idx
    return (suffix[idx] - thresholds * counts) / n


def sample_geometric_uniform(q: float, n: int, rng: np.random.Generator, tol: float = 1e-12) -> np.ndarray:
    """Sample X_q by summing until the total omitted support is at most tol."""
    j_max = max(1, int(math.ceil(math.log(tol) / math.log(q))))
    out = np.zeros(n)
    weight = 1.0 - q
    for _ in range(j_max):
        out += weight * rng.uniform(-1.0, 1.0, size=n)
        weight *= q
    return out


def experiment_convex_order(quick: bool) -> dict[str, float]:
    """Monte-Carlo diagnostic of the exact stop-loss inequalities."""
    r, s = 0.35, 0.72
    n = 500_000 if not quick else 120_000
    # Independent samples are enough for expectations; a common random stream
    # slightly reduces visual noise but is not used as a proof.
    rng_r = np.random.default_rng(20260830)
    rng_s = np.random.default_rng(20260831)
    xr = np.sort(sample_geometric_uniform(r, n, rng_r))
    xs = np.sort(sample_geometric_uniform(s, n, rng_s))
    thresholds = np.linspace(-1.0, 1.0, 241)
    call_r = empirical_stop_loss(xr, thresholds)
    call_s = empirical_stop_loss(xs, thresholds)
    gap = call_r - call_s

    with (DATA / "convex_order_stoploss.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["threshold", "call_r", "call_s", "gap"])
        writer.writerows(zip(thresholds, call_r, call_s, gap))

    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.plot(thresholds, gap, label=rf"$E(X_{{{r}}}-t)_+-E(X_{{{s}}}-t)_+$")
    ax.axhline(0.0, linewidth=1.0)
    ax.set_xlabel(r"threshold $t$")
    ax.set_ylabel("stop-loss gap")
    ax.set_title("Convex-order parameter flow: empirical diagnostic")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, "convex_order_stoploss")

    # Exact variance gap, used as an independent algebraic check.
    var_r = (1.0 - r) / (3.0 * (1.0 + r))
    var_s = (1.0 - s) / (3.0 * (1.0 + s))
    return {
        "convex_order_min_empirical_gap": float(np.min(gap)),
        "convex_order_max_empirical_gap": float(np.max(gap)),
        "variance_r": var_r,
        "variance_s": var_s,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="use smaller grids/sample sizes for a fast smoke test",
    )
    args = parser.parse_args()

    summary: dict[str, float] = {}
    summary.update(experiment_cgf(args.quick))
    summary.update(experiment_rate_function(args.quick))
    summary.update(experiment_edgeworth(args.quick))
    summary.update(experiment_convex_order(args.quick))

    with (DATA / "numerical_summary.txt").open("w") as f:
        f.write("Numerical summary for the q-Fabius frontier report\n")
        f.write("===================================================\n")
        f.write(f"quick_mode = {args.quick}\n")
        for key in sorted(summary):
            f.write(f"{key} = {summary[key]:.16g}\n")
    for key in sorted(summary):
        print(f"{key} = {summary[key]:.16g}")


if __name__ == "__main__":
    main()
