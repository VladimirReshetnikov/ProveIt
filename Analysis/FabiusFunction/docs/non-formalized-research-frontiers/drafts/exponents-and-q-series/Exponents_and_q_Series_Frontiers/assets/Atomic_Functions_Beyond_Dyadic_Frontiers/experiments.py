#!/usr/bin/env python3
"""Reproducible numerical audits for the Rvachev atomic-function report.

The script deliberately separates exact formulas from numerical checks.  Every
CSV row records either an exact value, a simulation/quadrature value, or both.
The figures are explanatory illustrations; none is used as a substitute for a
proof in the accompanying LaTeX report.

Dependencies: NumPy, Matplotlib, mpmath.  SciPy is not required.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

SEED = 20260828
RNG = np.random.default_rng(SEED)


def ensure_dirs(root: Path) -> tuple[Path, Path]:
    figures = root / "figures"
    data = root / "data"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)
    return figures, data


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def save_figure(fig: plt.Figure, figures: Path, stem: str) -> None:
    fig.tight_layout()
    fig.savefig(figures / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(figures / f"{stem}.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    """sin(x)/x, using NumPy's normalized sinc for stability at zero."""
    return np.sinc(np.asarray(x) / np.pi)


def phi_a(t: np.ndarray, a: float, terms: int | None = None) -> np.ndarray:
    """Truncated product Phi_a(t)=prod_{j>=1} sinc(t a^{-j}).

    The omitted factors are uniformly close to one.  The automatic truncation
    makes max(|t|) a^{-terms} below roughly 1e-10.
    """
    t = np.asarray(t, dtype=float)
    max_t = max(1.0, float(np.max(np.abs(t))))
    if terms is None:
        terms = max(20, int(math.ceil(math.log(max_t / 1e-10, a))))
    out = np.ones_like(t)
    scale = 1.0 / a
    for _ in range(terms):
        out *= sinc(t * scale)
        scale /= a
    return out


def sample_uniform_series(a: float, size: int, tol: float = 1e-12) -> np.ndarray:
    """Sample X_a=sum a^{-j}U_j with a deterministic tail bound below tol."""
    # Tail after J terms is a^{-J}/(a-1).
    terms = max(1, int(math.ceil(math.log(1.0 / (tol * (a - 1.0)), a))))
    out = np.zeros(size)
    scale = 1.0 / a
    for _ in range(terms):
        out += scale * RNG.uniform(-1.0, 1.0, size=size)
        scale /= a
    return out


def sample_bernoulli_sum(a: float, size: int, terms: int) -> np.ndarray:
    out = np.zeros(size)
    scale = 1.0 / a
    for _ in range(terms):
        out += scale * RNG.choice(np.array([-1.0, 1.0]), size=size)
        scale /= a
    return out


def empirical_cdf(samples: np.ndarray, grid: np.ndarray) -> np.ndarray:
    sorted_samples = np.sort(samples)
    return np.searchsorted(sorted_samples, grid, side="right") / sorted_samples.size


def central_gap_halfwidth(a: float) -> float:
    return (a - 2.0) / (a * (a - 1.0))


def gap_intervals(a: float, generation: int) -> list[tuple[float, float]]:
    b1 = central_gap_halfwidth(a)
    gaps = [(-b1, b1)]
    for _ in range(generation):
        next_gaps: list[tuple[float, float]] = []
        for left, right in gaps:
            next_gaps.append(((left - 1.0) / a, (right - 1.0) / a))
            next_gaps.append(((left + 1.0) / a, (right + 1.0) / a))
        gaps = sorted(next_gaps)
    return gaps


def exact_tube_volume(a: float, eps: np.ndarray) -> np.ndarray:
    b = 1.0 / (a - 1.0)
    ell0 = 2.0 * central_gap_halfwidth(a)
    out = np.empty_like(eps, dtype=float)
    for i, e in enumerate(eps):
        if e <= 0.0:
            out[i] = 0.0
        elif 2.0 * e >= ell0:
            # Directly sum min(2e, ell_n), which is stable for this range.
            total = 0.0
            for n in range(200):
                ell = ell0 * a ** (-n)
                contribution = (2.0**n) * min(2.0 * e, ell)
                total += contribution
                if (2.0**n) * ell < 1e-15:
                    break
            out[i] = min(total, 2.0 * b)
        else:
            n = math.floor(math.log(ell0 / (2.0 * e), a))
            out[i] = 2.0 * e * (2.0 ** (n + 1) - 1.0)
            out[i] += ell0 * (2.0 / a) ** (n + 1) / (1.0 - 2.0 / a)
    return out


def kappa_numpy(u: np.ndarray) -> np.ndarray:
    return np.log(-np.expm1(-u) / u)


def lambda_a_numpy(u: np.ndarray, a: float, tol: float = 1e-15) -> np.ndarray:
    out = np.zeros_like(u, dtype=float)
    scale = 1.0 / a
    # The small-u tail behaves as -u/(2(a-1)); stopping here is below tol.
    for _ in range(10000):
        v = u * scale
        out += kappa_numpy(v)
        if float(np.max(v)) < tol:
            break
        scale /= a
    return out


def r_tail_numpy(x: np.ndarray, a: float) -> np.ndarray:
    out = np.zeros_like(x, dtype=float)
    power = a**x
    for _ in range(1000):
        term = np.log1p(-np.exp(-power))
        out += term
        if float(np.max(np.abs(term))) < 1e-16:
            break
        power *= a
    return out


def periodic_p(a: float, x: np.ndarray) -> np.ndarray:
    L = math.log(a)
    u = a**x
    return lambda_a_numpy(u, a) + 0.5 * L * x*x - 0.5 * L * x + r_tail_numpy(x, a)


def cumulants_and_moments(a: float, max_order: int) -> tuple[list[float], list[float]]:
    """Return cumulants and moments through max_order by the Bell recurrence."""
    mp.mp.dps = 60
    cumulants = [0.0] * (max_order + 1)
    for n in range(2, max_order + 1, 2):
        m = n // 2
        value = (2 ** (2*m) * mp.bernoulli(2*m)) / (2*m * (a ** (2*m) - 1.0))
        cumulants[n] = float(value)
    moments = [0.0] * (max_order + 1)
    moments[0] = 1.0
    for n in range(1, max_order + 1):
        total = 0.0
        for j in range(1, n + 1):
            total += math.comb(n - 1, j - 1) * cumulants[j] * moments[n - j]
        moments[n] = total
    return cumulants, moments


def make_gap_hierarchy(figures: Path, data: Path) -> None:
    a = 2.6
    max_gen = 7
    rows: list[dict] = []
    fig, ax = plt.subplots(figsize=(9.2, 5.0))
    for n in range(max_gen + 1):
        for index, (left, right) in enumerate(gap_intervals(a, n)):
            ax.plot([left, right], [n, n], linewidth=4)
            rows.append({"generation": n, "index": index, "left": left, "right": right,
                         "length": right-left, "polynomial_degree": n})
    ax.set_xlabel("x")
    ax.set_ylabel("gap generation = polynomial degree")
    ax.set_title(r"Separated gap hierarchy for $a=2.6$")
    ax.invert_yaxis()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "gap_hierarchy_a_2_6")
    write_csv(data / "gap_geometry_a_2_6.csv",
              ["generation", "index", "left", "right", "length", "polynomial_degree"], rows)


def make_tube_oscillation(figures: Path, data: Path) -> None:
    a = 3.0
    ell0 = 2.0 * central_gap_halfwidth(a)
    D = math.log(2.0) / math.log(a)
    x = np.linspace(0.02, 9.0, 5000)
    eps = (ell0 / 2.0) * a**(-x)
    V = exact_tube_volume(a, eps)
    normalized = eps ** (D - 1.0) * V
    theta = x - np.floor(x)
    profile = ell0**D * (
        2.0 ** (2.0 - D - theta)
        + 2.0 ** (1.0 - D) * a ** ((D - 1.0) * (1.0 - theta)) / (1.0 - 2.0/a)
    )
    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    ax.plot(x, normalized, label=r"$\varepsilon^{D-1}V_a(\varepsilon)$")
    ax.plot(x, profile, linestyle="--", label="periodic profile")
    ax.set_xlabel(r"$\log_a(\ell_0/(2\varepsilon))$")
    ax.set_ylabel("normalized tube volume")
    ax.set_title(r"Exact logarithmic tube oscillation for $a=3$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "tube_oscillation_a_3")
    rows = [{"x": float(xi), "epsilon": float(e), "tube_volume": float(v),
             "normalized": float(nv), "periodic_profile": float(pr)}
            for xi, e, v, nv, pr in zip(x[::10], eps[::10], V[::10], normalized[::10], profile[::10])]
    write_csv(data / "tube_profile_a_3.csv",
              ["x", "epsilon", "tube_volume", "normalized", "periodic_profile"], rows)


def make_degree_limit(figures: Path, data: Path) -> None:
    x = np.linspace(0.0, 7.0, 1400)
    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    rows: list[dict] = []
    for a in [2.6, 2.25, 2.08, 2.02]:
        p = (a - 2.0) / a
        # N has P(N=n)=p(1-p)^n.  CDF of pN at x.
        k = np.floor(x / p).astype(int)
        cdf = 1.0 - (1.0 - p) ** (k + 1)
        ax.plot(x, cdf, label=f"a={a:g}")
        for xi, yi in zip(x[::70], cdf[::70]):
            rows.append({"a": a, "x": float(xi), "cdf": float(yi)})
    limit = 1.0 - np.exp(-x)
    ax.plot(x, limit, linestyle="--", label="Exp(1) limit")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("CDF of scaled local degree")
    ax.set_title("Critical local-degree limit")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "degree_critical_limit")
    write_csv(data / "degree_critical_limit.csv", ["a", "x", "cdf"], rows)


def make_distance_law(figures: Path, data: Path) -> None:
    a = 3.0
    b = 1.0 / (a - 1.0)
    ell0 = 2.0 * central_gap_halfwidth(a)
    r = np.linspace(0.0, ell0/2.0, 1600)
    V = exact_tube_volume(a, r)
    exact_survival = 1.0 - V/(2.0*b)
    exact_survival[0] = 1.0

    size = 350_000
    p = (a - 2.0) / a
    N = RNG.geometric(p, size=size) - 1
    U = RNG.random(size)
    delta = 0.5 * ell0 * a**(-N) * U
    sim_survival = 1.0 - empirical_cdf(delta, r)

    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    ax.plot(r, exact_survival, label="exact")
    ax.plot(r, sim_survival, linestyle="--", label="simulation")
    ax.set_xlabel(r"$r$")
    ax.set_ylabel("survival probability")
    ax.set_title(r"Distance to the nonanalytic set for $a=3$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "distance_to_singular_set_a_3")

    rows: list[dict] = []
    for s in [0.5, 1.0, 2.0, 3.0]:
        exact = ((a-2.0)/a) * (ell0/2.0)**s / ((s+1.0)*(1.0-2.0*a**(-(s+1.0))))
        observed = float(np.mean(delta**s))
        rows.append({"quantity": f"moment_s={s}", "exact": exact, "observed": observed,
                     "absolute_error": abs(exact-observed)})
    rows.append({"quantity": "max_cdf_error", "exact": 0.0,
                 "observed": float(np.max(np.abs(exact_survival-sim_survival))),
                 "absolute_error": float(np.max(np.abs(exact_survival-sim_survival)))})
    write_csv(data / "distance_validation_a_3.csv",
              ["quantity", "exact", "observed", "absolute_error"], rows)


def make_energy_limit(figures: Path, data: Path) -> None:
    a = 3.0
    b = 1.0/(a-1.0)
    size = 300_000
    grid = np.linspace(-b, b, 1800)
    limit = sample_bernoulli_sum(a, size, terms=28)
    limit_cdf = empirical_cdf(limit, grid)

    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    rows: list[dict] = []
    # p=1 means Y has density h_a and can be sampled directly as X_a.
    for n in [0, 1, 3, 6]:
        if n == 0:
            samples = sample_uniform_series(a, size)
        else:
            prefix = sample_bernoulli_sum(a, size, terms=n)
            base = sample_uniform_series(a, size)
            samples = prefix + a**(-n) * base
        cdf = empirical_cdf(samples, grid)
        ax.plot(grid, cdf, label=f"n={n}")
        kol = float(np.max(np.abs(cdf-limit_cdf)))
        exact_winf = 2.0*a**(-n)/(a-1.0)
        b1 = central_gap_halfwidth(a)
        hausdorff = b1*a**(-n)
        entropy_shift = n*math.log(2.0/a)
        rows.append({"n": n, "empirical_kolmogorov": kol,
                     "exact_W_infinity_bound": exact_winf,
                     "exact_support_Hausdorff": hausdorff,
                     "exact_entropy_shift": entropy_shift})
    ax.plot(grid, limit_cdf, linestyle="--", linewidth=2.0, label=r"limit $\nu_3$")
    ax.set_xlabel("x")
    ax.set_ylabel("empirical CDF")
    ax.set_title(r"Normalized derivative-energy convergence ($a=3$, $p=1$)")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "derivative_energy_cantor_limit_a_3")
    write_csv(data / "energy_cantor_convergence_a_3_p_1.csv",
              ["n", "empirical_kolmogorov", "exact_W_infinity_bound",
               "exact_support_Hausdorff", "exact_entropy_shift"], rows)


def make_periodic_correction(figures: Path, data: Path) -> None:
    x = np.linspace(0.0, 1.0, 4096, endpoint=False)
    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    rows_period: list[dict] = []
    for a in [1.2, 1.5, 2.0, 2.6, 3.0, 5.0]:
        P = periodic_p(a, x)
        centered = P - np.mean(P)
        ax.plot(x, centered, label=f"a={a:g}")
        P_shift = periodic_p(a, x+1.0)
        rows_period.append({"a": a,
                            "max_periodicity_residual": float(np.max(np.abs(P_shift-P))),
                            "peak_to_peak_centered": float(np.ptp(centered))})
    ax.set_xlabel("logarithmic phase x")
    ax.set_ylabel(r"$P_a(x)-\overline{P}_a$")
    ax.set_title("General-base periodic Laplace correction")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "periodic_correction_bases")
    write_csv(data / "periodicity_residuals.csv",
              ["a", "max_periodicity_residual", "peak_to_peak_centered"], rows_period)

    mp.mp.dps = 60
    rows_modes: list[dict] = []
    for a in [1.5, 2.0, 2.6, 3.0, 5.0]:
        P = periodic_p(a, x)
        centered = P - np.mean(P)
        L = math.log(a)
        for k in range(1, 5):
            numeric = np.mean(centered*np.exp(-2j*np.pi*k*x))
            chi = 2j*mp.pi*k/mp.log(a)
            exact_mp = -mp.gamma(-chi)*mp.zeta(1-chi)/mp.log(a)
            exact = complex(exact_mp)
            rows_modes.append({"a": a, "k": k,
                               "numeric_real": numeric.real, "numeric_imag": numeric.imag,
                               "exact_real": exact.real, "exact_imag": exact.imag,
                               "absolute_error": abs(numeric-exact)})
    write_csv(data / "gamma_zeta_fourier_validation.csv",
              ["a", "k", "numeric_real", "numeric_imag", "exact_real", "exact_imag",
               "absolute_error"], rows_modes)


def make_gaussian_limit(figures: Path, data: Path) -> None:
    a = np.linspace(1.0005, 1.35, 1200)
    exact = -(6.0/5.0)*(a*a-1.0)/(a*a+1.0)
    first = -(6.0/5.0)*(a-1.0)
    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    ax.plot(a, exact, label="exact standardized fourth cumulant")
    ax.plot(a, first, linestyle="--", label="first asymptotic term")
    ax.set_xlabel("a")
    ax.set_ylabel(r"$\lambda_4(a)$")
    ax.set_title(r"Gaussian cumulant scaling as $a\downarrow1$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "gaussian_cumulant_limit")
    rows = [{"a": float(ai), "exact_lambda4": float(e), "first_term": float(f),
             "absolute_error": float(abs(e-f))}
            for ai, e, f in zip(a[::30], exact[::30], first[::30])]
    write_csv(data / "gaussian_cumulant_limit.csv",
              ["a", "exact_lambda4", "first_term", "absolute_error"], rows)


def make_moment_validation(data: Path) -> None:
    a = 2.6
    _, moments = cumulants_and_moments(a, 10)
    samples = sample_uniform_series(a, 250_000)
    rows: list[dict] = []
    for n in range(0, 11):
        observed = float(np.mean(samples**n))
        exact = moments[n]
        rows.append({"order": n, "exact_moment": exact, "monte_carlo": observed,
                     "absolute_error": abs(exact-observed)})
    write_csv(data / "moment_validation_a_2_6.csv",
              ["order", "exact_moment", "monte_carlo", "absolute_error"], rows)


def spectral_integrals(a: float, max_n: int) -> list[float]:
    # Logarithmic t-grid.  The moment n=4 is concentrated around t of order 10^2,
    # while the tails are already far below double precision by t=e^14.
    u = np.linspace(-22.0, 14.0, 240_000)
    t = np.exp(u)
    phi = phi_a(t, a)
    base = phi*phi
    values: list[float] = []
    for n in range(max_n+1):
        integrand = np.exp((2*n+1)*u)*base
        values.append(2.0*float(np.trapezoid(integrand, u)))
    return values


def make_spectral_twin(figures: Path, data: Path) -> None:
    a = 2.6
    z = np.logspace(-5.0, 5.0, 8000)
    t = np.sqrt(z)
    phi = phi_a(t, a)
    integrals = spectral_integrals(a, 4)
    I = integrals[0]
    w_sp = phi*phi/(I*np.sqrt(z))
    mu = 2.0*math.log(a)-math.log(2.0)
    sigma2 = 2.0*math.log(a)
    w_ln = np.exp(-(np.log(z)-mu)**2/(2.0*sigma2))/(z*math.sqrt(2.0*math.pi*sigma2))
    # Plot the density of log Z, namely z w(z), to avoid a misleading singularity at zero.
    fig, ax = plt.subplots(figsize=(9.2, 4.8))
    ax.semilogx(z, z*w_sp, label="sinc-product spectral law")
    ax.semilogx(z, z*w_ln, linestyle="--", label="lognormal moment twin")
    ax.set_xlabel("z")
    ax.set_ylabel(r"density of $\log Z$: $z w(z)$")
    ax.set_title(r"Distinct moment twins for $a=2.6$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures, "spectral_lognormal_general_base")

    rows: list[dict] = []
    for n, integral in enumerate(integrals):
        observed = integral/I
        exact = a**(n*(n+2))/(2.0**n)
        rows.append({"order": n, "quadrature_moment": observed, "exact_moment": exact,
                     "relative_error": abs(observed-exact)/exact if exact else 0.0})
    write_csv(data / "spectral_moment_validation_a_2_6.csv",
              ["order", "quadrature_moment", "exact_moment", "relative_error"], rows)

    zq = np.logspace(-4.0, 3.0, 5000)
    left = phi_a(a*np.sqrt(zq), a)**2/(I*a*np.sqrt(zq))
    right = (1.0/a)*sinc(np.sqrt(zq))**2 * (phi_a(np.sqrt(zq), a)**2/(I*np.sqrt(zq)))
    residual = np.abs(left-right)
    rows_q = [{"z": float(zz), "left": float(ll), "right": float(rr),
               "absolute_residual": float(res)}
              for zz, ll, rr, res in zip(zq[::50], left[::50], right[::50], residual[::50])]
    write_csv(data / "spectral_q_pearson_validation_a_2_6.csv",
              ["z", "left", "right", "absolute_residual"], rows_q)


def make_derivative_norm_table(data: Path) -> None:
    rows: list[dict] = []
    for a in [2.0, 2.6, 3.0, 5.0]:
        for n in range(0, 9):
            linf = a**(((n+1)*(n+2))/2.0)/(2.0**(n+1))
            l1 = a**(n*(n+1)/2.0)
            support = 2.0/(a-1.0)*(2.0/a)**n
            rows.append({"a": a, "n": n, "L_infinity": linf,
                         "L1": l1, "essential_support_measure": support})
    write_csv(data / "derivative_norms_and_support.csv",
              ["a", "n", "L_infinity", "L1", "essential_support_measure"], rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent,
                        help="report directory containing figures/ and data/")
    args = parser.parse_args()
    figures, data = ensure_dirs(args.output)

    make_gap_hierarchy(figures, data)
    make_tube_oscillation(figures, data)
    make_degree_limit(figures, data)
    make_distance_law(figures, data)
    make_energy_limit(figures, data)
    make_periodic_correction(figures, data)
    make_gaussian_limit(figures, data)
    make_moment_validation(data)
    make_spectral_twin(figures, data)
    make_derivative_norm_table(data)
    print(f"Wrote figures to {figures}")
    print(f"Wrote data tables to {data}")


if __name__ == "__main__":
    main()
