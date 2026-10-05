#!/usr/bin/env python3
"""Reproduce the geometric-occupancy article's deterministic numerical checks.

No random sampling is used.  The exact computations use fractions.Fraction;
the larger computations use log-sum-exp recurrences.  Numerical agreement is
evidence about the formulas and the implementation, not a proof of a limit
theorem.  Run ``python verify_occupancy.py`` from any directory.

For 0 < q < 1 put c_j=(1-q)q**j and condition sum_j K_j=m, with weight
    prod_j c_j**(2*K_j)/(K_j!*(2*K_j+1)!!).
If Y=sum_j c_j U_j, U_j uniform on [-1,1], its even moments mu[m] satisfy
    (1-q**(2*m))*mu[m] = sum_{k=1}^m
       binom(2*m,2*k)*(1-q)**(2*k)*q**(2*m-2*k)*mu[m-k]/(2*k+1).
The marginal P_m(K_0=k) has the same summand, including k=0, divided by mu[m].
The factor 2**m between this model's weights and exponential-moment
coefficients cancels after conditioning.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import platform
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gammaln, logsumexp


def even_moments_exact(q: Fraction, maximum: int) -> list[Fraction]:
    """Exact even moments of the infinite random uniform sum."""
    mu = [Fraction(1)]
    c = 1 - q
    for m in range(1, maximum + 1):
        numerator = sum(
            (Fraction(math.comb(2 * m, 2 * k), 2 * k + 1)
             * c ** (2 * k) * q ** (2 * (m - k)) * mu[m - k]
             for k in range(1, m + 1)),
            Fraction(0),
        )
        mu.append(numerator / (1 - q ** (2 * m)))
    return mu


def marginal_exact(q: Fraction, mu: list[Fraction], m: int) -> list[Fraction]:
    c = 1 - q
    return [
        Fraction(math.comb(2 * m, 2 * k), 2 * k + 1)
        * c ** (2 * k) * q ** (2 * (m - k)) * mu[m - k] / mu[m]
        for k in range(m + 1)
    ]


def exact_checks(q: Fraction, maximum: int, output: Path) -> dict:
    """Check probability identities using independent coefficient formulas."""
    mu = even_moments_exact(q, maximum)
    marginal = [marginal_exact(q, mu, m) for m in range(maximum + 1)]
    means = [sum((k * p for k, p in enumerate(row)), Fraction(0))
             for row in marginal]
    coeff = [mu[m] / math.factorial(2 * m) for m in range(maximum + 1)]
    c0, c1 = 1 - q, (1 - q) * q
    rows = []
    for m in range(maximum + 1):
        p = marginal[m]
        assert sum(p, Fraction(0)) == 1
        assert all(v > 0 for v in p)
        assert p[0] == q ** (2 * m)
        mean0 = means[m]
        var0 = sum(((k - mean0) ** 2 * pk for k, pk in enumerate(p)),
                   Fraction(0))
        mean1 = sum((pk * means[m - k] for k, pk in enumerate(p)),
                    Fraction(0))
        cov01 = sum(((k - mean0) * (means[m - k] - mean1) * pk
                     for k, pk in enumerate(p)), Fraction(0))

        # Directly extract two head variables and the independent scaled tail.
        # This verifies the conditional self-similarity and covariance formula
        # without evaluating either through a second copy of that recursion.
        direct_mass = Fraction(0)
        direct_mean1 = Fraction(0)
        direct_cross = Fraction(0)
        for k in range(m + 1):
            for ell in range(m - k + 1):
                rest = m - k - ell
                joint = (c0 ** (2 * k) / math.factorial(2 * k + 1)
                         * c1 ** (2 * ell) / math.factorial(2 * ell + 1)
                         * q ** (4 * rest) * coeff[rest] / coeff[m])
                assert joint == p[k] * marginal[m - k][ell]
                direct_mass += joint
                direct_mean1 += ell * joint
                direct_cross += k * ell * joint
        assert direct_mass == 1
        assert direct_mean1 == mean1
        assert direct_cross - mean0 * mean1 == cov01
        assert var0 >= 0
        if m:
            assert cov01 < 0
        rows.append({
            "m": m,
            "mu_2m_exact": str(mu[m]),
            "mean_K0_exact": str(mean0),
            "mean_K1_exact": str(mean1),
            "var_K0_exact": str(var0),
            "cov_K0_K1_exact": str(cov01),
        })
    write_csv(output / "exact_checks.csv", rows)

    # A finite product gives the exact CDF of the largest occupied index.
    head = [Fraction(1)] + [Fraction(0)] * maximum
    previous = [Fraction(0)] * (maximum + 1)
    max_rows = []
    for j in range(13):
        c = (1 - q) * q ** j
        site = [c ** (2 * k) / math.factorial(2 * k + 1)
                for k in range(maximum + 1)]
        head = [sum((head[m - k] * site[k] for k in range(m + 1)),
                    Fraction(0)) for m in range(maximum + 1)]
        for m in range(1, maximum + 1):
            probability = head[m] / coeff[m]
            assert previous[m] <= probability <= 1
            if j == 0:
                assert probability == marginal[m][m]
            previous[m] = probability
            if m in {1, 2, 4, 8, maximum}:
                max_rows.append({"m": m, "J": j,
                                 "P_max_le_J_exact": str(probability),
                                 "P_max_le_J": float(probability)})
    write_csv(output / "exact_maximum_cdf.csv", max_rows)
    return {"q_exact": str(q), "largest_exact_m": maximum,
            "all_exact_checks_passed": True,
            "mu_float": [float(x) for x in mu]}


def log_moments_and_occupancies(q: float, maximum: int) -> tuple[np.ndarray, dict]:
    """Log-domain moments and centered first/two-site statistics."""
    logq, logc = math.log(q), math.log1p(-q)
    twice = 2 * np.arange(maximum + 1)
    logfact_even = gammaln(twice + 1)
    logfact_odd = gammaln(twice + 2)
    logmu = np.zeros(maximum + 1)
    mean0 = np.zeros(maximum + 1)
    mean1 = np.zeros(maximum + 1)
    var0 = np.zeros(maximum + 1)
    var1 = np.zeros(maximum + 1)
    cov01 = np.zeros(maximum + 1)
    occupied_mean = np.zeros(maximum + 1)
    occupied_var = np.zeros(maximum + 1)
    max_norm_defect = 0.0
    minimum_variance = math.inf
    for m in range(1, maximum + 1):
        k = np.arange(1, m + 1)
        rest = m - k
        summands = (logfact_even[m] - logfact_odd[k] - logfact_even[rest]
                    + 2 * k * logc + 2 * rest * logq + logmu[rest])
        # -expm1 is accurate if q is close to 1.
        logmu[m] = logsumexp(summands) - math.log(-math.expm1(2 * m * logq))
        k = np.arange(m + 1)
        rest = m - k
        logp = (logfact_even[m] - logfact_odd[k] - logfact_even[rest]
                + 2 * k * logc + 2 * rest * logq + logmu[rest] - logmu[m])
        lognorm = float(logsumexp(logp))
        max_norm_defect = max(max_norm_defect, abs(math.expm1(lognorm)))
        p = np.exp(logp - lognorm)
        assert np.all(np.isfinite(p)) and np.all(p >= 0)
        assert abs(float(np.sum(p)) - 1) < 3e-14
        mean0[m] = np.dot(p, k)
        var0[m] = np.dot(p, (k - mean0[m]) ** 2)
        # The residual occupancy has exactly the same normalized coefficients.
        residual_mean = mean0[rest]
        mean1[m] = np.dot(p, residual_mean)
        cov01[m] = np.dot(p, (k - mean0[m]) * (residual_mean - mean1[m]))
        var1[m] = np.dot(p, var0[rest] + (residual_mean - mean1[m]) ** 2)
        # Skip the possibly empty first site.  Conditional on a positive
        # first occupancy, the remaining occupied count is H_(m-k).
        first_positive = p[1:] / np.sum(p[1:])
        positive_rest = rest[1:]
        occupied_mean[m] = 1 + np.dot(first_positive, occupied_mean[positive_rest])
        occupied_var[m] = np.dot(
            first_positive, occupied_var[positive_rest]
            + (1 + occupied_mean[positive_rest] - occupied_mean[m]) ** 2)
        minimum_variance = min(minimum_variance, var0[m], var1[m])
    assert minimum_variance > 0
    assert np.all(cov01[1:] < 0)
    return logmu, {"mean0": mean0, "mean1": mean1, "var0": var0,
                   "var1": var1, "cov01": cov01,
                   "occupied_mean": occupied_mean, "occupied_var": occupied_var,
                   "max_raw_probability_normalization_defect": max_norm_defect}


def positive_sinh_series(a: float) -> tuple[float, float]:
    """Positive series for sinh(a)/a and its occupancy-weighted numerator."""
    term, denominator, numerator = 1.0, 1.0, 0.0
    for k in range(1, 100):
        term *= a * a / ((2 * k) * (2 * k + 1))
        denominator += term
        numerator += k * term
        if term < 2e-18 * max(numerator, 1e-300):
            break
    return denominator, numerator


def occupancy_mean(a: float) -> float:
    """h(a)=(a*coth(a)-1)/2, with no small-a cancellation."""
    if a == 0:
        return 0.0
    if a < 0.25:
        denominator, numerator = positive_sinh_series(a)
        return numerator / denominator
    if a > 20:
        u = math.exp(-2 * a)
        return (a - 1) / 2 + a * u / (1 - u)
    return (a / math.tanh(a) - 1) / 2


def log_vacancy(a: float) -> float:
    """log(a/sinh(a)), evaluated stably in the small and large regimes."""
    if a == 0:
        return 0.0
    if a < 0.25:
        term, remainder = 1.0, 0.0
        for k in range(1, 100):
            term *= a * a / ((2 * k) * (2 * k + 1))
            remainder += term
            if term < 2e-18 * max(remainder, 1e-300):
                break
        return -math.log1p(remainder)
    if a > 20:
        return math.log(2 * a) - a - math.log1p(-math.exp(-2 * a))
    return math.log(a / math.sinh(a))


def occupancy_probabilities(a: float, maximum: int = 12) -> np.ndarray:
    """P(Z_a=k)=a^(2k+1)/((2k+1)!sinh(a)), k=0,...,maximum."""
    if a == 0:
        return np.r_[1.0, np.zeros(maximum)]
    k = np.arange(maximum + 1)
    return np.exp(2 * k * math.log(a) - gammaln(2 * k + 2) + log_vacancy(a))


def saddle_sum(t: float, q: float, tolerance: float = 2e-15) -> tuple[float, float]:
    """Sum_j h(t*(1-q)*q**j), with a bound on the omitted positive tail.

    The partial fraction formula for coth gives 0 <= h(a) <= a^2/6.
    Therefore the omitted tail after the next argument a is at most
    a^2/[6*(1-q^2)].
    """
    a, terms = t * (1 - q), []
    for _ in range(100000):
        terms.append(occupancy_mean(a))
        a *= q
        bound = a * a / (6 * (1 - q * q))
        if bound < tolerance:
            return math.fsum(terms), bound
    raise RuntimeError("Saddle tail did not meet the requested tolerance")


def exact_saddle(m: int, q: float) -> dict:
    """Numerically solve the exact saddle equation, not an asymptotic proxy."""
    lo, hi = 2.0 * m, 2.0 * m + 2.0
    while saddle_sum(hi, q)[0] < m:
        hi *= 2
    t = brentq(lambda x: saddle_sum(x, q)[0] - m, lo, hi,
               xtol=2e-12, rtol=1e-14)
    value, tail_bound = saddle_sum(t, q)
    position = math.log(t * (1 - q)) / -math.log(q)
    n = math.floor(position)
    return {"t": t, "n": n, "theta": position - n,
            "residual": value - m, "tail_bound": tail_bound}


def limiting_maximum_cdf(q: float, theta: float, s: int,
                         tolerance: float = 2e-16) -> tuple[float, float]:
    """Product_{r>s} a_r/sinh(a_r), with an omitted-log-tail error bound."""
    a, logs = q ** (s + 1 - theta), []
    for _ in range(100000):
        logs.append(log_vacancy(a))
        a *= q
        bound = a * a / (6 * (1 - q * q))
        if bound < tolerance:
            return math.exp(math.fsum(logs)), bound
    raise RuntimeError("Maximum-CDF tail did not meet the requested tolerance")


def limiting_occupied_count(q: float, theta: float) -> tuple[float, float]:
    """Mean and variance of the bilateral frontier occupied-count limit."""
    mean_terms, variance_terms = [], []
    r = 0
    while True:
        a = q ** (r - theta)
        b = math.exp(log_vacancy(a))
        mean_terms.append(-b)
        variance_terms.append(b * -math.expm1(log_vacancy(a)))
        if b < 1e-18:
            break
        r -= 1
    r = 1
    while True:
        a = q ** (r - theta)
        logb = log_vacancy(a)
        vacancy, occupation = math.exp(logb), -math.expm1(logb)
        mean_terms.append(occupation)
        variance_terms.append(vacancy * occupation)
        if (a * q) ** 2 / (6 * (1 - q * q)) < 2e-17:
            break
        r += 1
    return math.fsum(mean_terms), math.fsum(variance_terms)


def l1_constant(q: float) -> tuple[float, float]:
    """Sum_j sqrt(c_j*(1-c_j))/sqrt(pi), with a geometric tail bound."""
    terms, c = [], 1 - q
    for _ in range(100000):
        terms.append(math.sqrt(c * (1 - c) / math.pi))
        c *= q
        tail_bound = math.sqrt(c / math.pi) / (1 - math.sqrt(q))
        if tail_bound < 1e-15:
            return math.fsum(terms), tail_bound
    raise RuntimeError("l1-constant tail did not meet the requested tolerance")


def finite_maximum_checks(q: float, logmu: np.ndarray,
                          saddles: dict[int, dict], output: Path) -> dict:
    """Direct finite-product coefficients; no independence approximation."""
    maximum = len(logmu) - 1
    selected = sorted({m for m in (16, 64, 256, 1024, maximum) if m <= maximum})
    max_j = max(saddles[m]["n"] + 5 for m in selected)
    k_all = np.arange(maximum + 1)
    full_coeff = logmu - gammaln(2 * k_all + 1)
    head = np.full(maximum + 1, -np.inf)
    head[0] = 0.0
    rows = []
    for j in range(max_j + 1):
        logc = math.log1p(-q) + j * math.log(q)
        site = 2 * k_all * logc - gammaln(2 * k_all + 2)
        next_head = np.empty_like(head)
        for m in range(maximum + 1):
            next_head[m] = logsumexp(head[:m + 1][::-1] + site[:m + 1])
        head = next_head
        for m in selected:
            n, theta = saddles[m]["n"], saddles[m]["theta"]
            s = j - n
            if -3 <= s <= 5:
                logcdf = float(head[m] - full_coeff[m])
                assert logcdf < 2e-10
                exact_cdf = math.exp(min(0.0, logcdf))
                limit_cdf, tail_bound = limiting_maximum_cdf(q, theta, s)
                rows.append({"m": m, "J": j, "s": s,
                             "theta_m": theta, "finite_CDF": exact_cdf,
                             "phase_limit_CDF": limit_cdf,
                             "absolute_difference": abs(exact_cdf - limit_cdf),
                             "limit_omitted_log_tail_bound": tail_bound})
    write_csv(output / "finite_maximum_comparison.csv", rows)
    return {str(m): max(row["absolute_difference"] for row in rows if row["m"] == m)
            for m in selected}


def finite_l1_checks(q: float, logmu: np.ndarray, constant: float,
                     output: Path) -> list[dict]:
    """Compute the complete expected l1 discrepancy with a controlled tail.

    After j sites the residual total R_j is a finite-state Markov chain.
    Its transition r -> ell is P_r(K_0=r-ell).  For sites beyond J,
       sum E|K_j-m*c_j| <= E R_(J+1) + m*q**(J+1).
    Only this deterministic tail is bounded; roundoff is not included.
    """
    maximum = len(logmu) - 1
    k_all = np.arange(maximum + 1)
    even_factorials = gammaln(2 * k_all + 1)
    odd_factorials = gammaln(2 * k_all + 2)
    pmf = np.zeros((maximum + 1, maximum + 1))
    transition = np.zeros_like(pmf)
    pmf[0, 0] = transition[0, 0] = 1.0
    for m in range(1, maximum + 1):
        k = np.arange(m + 1)
        rest = m - k
        logp = (even_factorials[m] - odd_factorials[k] - even_factorials[rest]
                + 2 * k * math.log1p(-q) + 2 * rest * math.log(q)
                + logmu[rest] - logmu[m])
        pmf[m, :m + 1] = np.exp(logp - logsumexp(logp))
        transition[m, :m + 1] = pmf[m, :m + 1][::-1]
    rows = []
    for m in sorted({x for x in (16, 64, 256, 1024, maximum) if x <= maximum}):
        residual = np.zeros(m + 1)
        residual[m] = 1
        total, index = 0.0, np.arange(m + 1)
        for j in range(100000):
            marginal = residual @ pmf[:m + 1, :m + 1]
            total += float(marginal @ np.abs(index - m * (1 - q) * q ** j))
            residual = residual @ transition[:m + 1, :m + 1]
            tail = (float(residual @ index) + m * q ** (j + 1)) / math.sqrt(m)
            if tail < 1e-11:
                break
        else:
            raise RuntimeError("l1 discrepancy tail did not converge")
        rows.append({"m": m,
                     "sqrt_m_expected_l1_partial_sum": total / math.sqrt(m),
                     "omitted_tail_upper_bound": tail,
                     "last_included_site": j, "Gaussian_limit_constant": constant})
    write_csv(output / "l1_convergence.csv", rows)
    return rows


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def make_figures(q: float, stats: dict, rows: list[dict], output: Path) -> None:
    """Two vector-PDF figures, with matching PNG previews for inspection."""
    colors = ["#18667D", "#C26435", "#7A619D"]
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 11.5,
        "axes.titlesize": 11.8, "axes.labelsize": 11.5,
        "xtick.labelsize": 11, "ytick.labelsize": 11,
        "legend.fontsize": 11, "axes.spines.top": False,
        "axes.spines.right": False, "axes.edgecolor": "#6D7880",
        "axes.labelcolor": "#263841", "text.color": "#263841",
        "xtick.color": "#52636B", "ytick.color": "#52636B",
        "grid.color": "#DDE4E8", "grid.linewidth": 0.65,
        "pdf.fonttype": 42, "ps.fonttype": 42,
    })
    m = np.arange(1, len(stats["mean0"]))
    c0, c1 = 1 - q, (1 - q) * q
    fig, axes = plt.subplots(1, 3, figsize=(8.4, 3.8), layout="constrained")
    ax = axes[0]
    for key, coefficient, color, label in (
            ("mean0", c0, colors[0], r"$K_0$"),
            ("mean1", c1, colors[1], r"$K_1$")):
        ax.plot(m, stats[key][1:] / m, color=color, lw=1.9, label=label)
        ax.axhline(coefficient, color=color, lw=1.0, ls=(0, (3, 3)), alpha=0.75)
    ax.set_title("(a) Mean occupancy")
    ax.set_ylabel(r"$\mathbb{E}K_j/m$")
    ax.legend(frameon=False, loc="upper right")
    ax = axes[1]
    for key, coefficient, color, label in (
            ("var0", c0, colors[0], r"$K_0$"),
            ("var1", c1, colors[1], r"$K_1$")):
        ax.plot(m, stats[key][1:] / m, color=color, lw=1.9, label=label)
        ax.axhline(coefficient * (1 - coefficient) / 2,
                   color=color, lw=1.0, ls=(0, (3, 3)), alpha=0.75)
    ax.set_title("(b) Variance")
    ax.set_ylabel(r"$\mathrm{Var}(K_j)/m$")
    ax.legend(frameon=False, loc="center right")
    ax = axes[2]
    ax.plot(m, stats["cov01"][1:] / m, color=colors[2], lw=1.9,
            label=r"Finite $m$")
    ax.axhline(-c0 * c1 / 2, color="#435762", lw=1.0, ls=(0, (3, 3)),
               label="Gaussian limit")
    ax.set_title("(c) Covariance")
    ax.set_ylabel(r"$\mathrm{Cov}(K_0,K_1)/m$")
    ax.legend(frameon=False, loc="lower right", handlelength=1.4,
              handletextpad=0.5, borderaxespad=0.3)
    for ax in axes:
        ax.set_xscale("log", base=2)
        ax.set_xlim(1, m[-1])
        ax.set_xticks([v for v in (1, 8, 64, 1024) if v <= m[-1]])
        ax.xaxis.set_major_formatter(matplotlib.ticker.ScalarFormatter())
        ax.set_xlabel(r"Total occupancy $m$")
        ax.grid(axis="y")
    save_figure(fig, output / "occupancy_convergence")

    plt.rcParams.update({"font.size": 11, "axes.titlesize": 11.5,
                         "axes.labelsize": 11, "legend.fontsize": 10.5})
    fig, axes = plt.subplots(1, 2, figsize=(7.4, 3.8), layout="constrained",
                             gridspec_kw={"width_ratios": [1.04, 1]})
    s = np.arange(-5, 7)
    for theta, color in zip((0.0, 0.5, 0.9), colors):
        cdf = [limiting_maximum_cdf(q, theta, int(v))[0] for v in s]
        axes[0].step(s, cdf, where="post", color=color, lw=1.75,
                     label=rf"$\theta={theta:g}$")
        axes[0].plot(s, cdf, "o", ms=3.0, color=color)
    axes[0].set_title("(a) Limiting last occupied site")
    axes[0].set_xlabel(r"Relative site $s$")
    axes[0].set_ylabel(r"$\Pr(M-n\leq s)$")
    axes[0].set_xlim(-5, 5.5)
    axes[0].set_ylim(-0.02, 1.04)
    axes[0].set_xticks(np.arange(-5, 6))
    axes[0].grid(axis="y")
    axes[0].legend(frameon=False, loc="lower right")

    r = np.arange(-3, 5)
    theta = 0.5
    probabilities = np.array([occupancy_probabilities(q ** (v - theta), 1) for v in r])
    vacancy = probabilities[:, 0]
    one = probabilities[:, 1]
    many = np.maximum(0.0, 1.0 - vacancy - one)
    axes[1].bar(r, vacancy, color="#CCDDE3", width=0.73, label=r"$Z=0$")
    axes[1].bar(r, one, bottom=vacancy, color=colors[0], width=0.73, label=r"$Z=1$")
    axes[1].bar(r, many, bottom=vacancy + one, color=colors[1], width=0.73,
                label=r"$Z\geq 2$")
    axes[1].set_title(r"(b) Frontier at $\theta=0.5$")
    axes[1].set_xlabel(r"Relative site $r=j-n$")
    axes[1].set_ylabel("Probability")
    axes[1].set_ylim(0, 1.03)
    axes[1].set_xticks(r)
    axes[1].legend(frameon=False, loc="upper center", ncol=3,
                   bbox_to_anchor=(0.5, -0.24), borderaxespad=0.2,
                   handlelength=1.2, handletextpad=0.45, columnspacing=1.1)
    save_figure(fig, output / "frontier_limits")


def save_figure(fig: plt.Figure, stem: Path) -> None:
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight",
                metadata={"Creator": "verify_occupancy.py / Matplotlib",
                          "CreationDate": None, "ModDate": None})
    fig.savefig(stem.with_suffix(".png"), dpi=190, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", default="1/2", help="Ratio, e.g. 1/2 or 0.7")
    parser.add_argument("--max-m", type=int, default=1024)
    parser.add_argument("--exact-max", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    q_exact = Fraction(args.q)
    q = float(q_exact)
    if not 0 < q < 1 or args.max_m < 16 or not 1 <= args.exact_max <= args.max_m:
        parser.error("Require 0<q<1, max-m>=16, and 1<=exact-max<=max-m")
    output = args.output.resolve()
    data, figures = output / "data", output / "figures"
    data.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)
    exact = exact_checks(q_exact, args.exact_max, data)
    logmu, stats = log_moments_and_occupancies(q, args.max_m)
    max_exact_moment_relative_error = float(np.max(np.abs(
        np.exp(logmu[:args.exact_max + 1]) / np.array(exact.pop("mu_float")) - 1)))
    assert max_exact_moment_relative_error < 2e-12
    saddles, rows = {}, []
    for m in range(1, args.max_m + 1):
        saddle = exact_saddle(m, q)
        saddles[m] = saddle
        count_mean, count_var = limiting_occupied_count(q, saddle["theta"])
        rows.append({
            "m": m, "log_mu_2m": logmu[m],
            "mean_K0_over_m": stats["mean0"][m] / m,
            "mean_K1_over_m": stats["mean1"][m] / m,
            "var_K0_over_m": stats["var0"][m] / m,
            "var_K1_over_m": stats["var1"][m] / m,
            "cov_K0_K1_over_m": stats["cov01"][m] / m,
            "saddle_t": saddle["t"], "t_minus_2m": saddle["t"] - 2 * m,
            "frontier_n": saddle["n"], "frontier_theta": saddle["theta"],
            "saddle_residual": saddle["residual"],
            "saddle_omitted_tail_bound": saddle["tail_bound"],
            "occupied_count_mean": stats["occupied_mean"][m],
            "occupied_count_variance": stats["occupied_var"][m],
            "occupied_count_phase_mean_prediction": saddle["n"] + 1 + count_mean,
            "occupied_count_phase_variance_prediction": count_var,
        })
    write_csv(data / "bulk_statistics.csv", rows)

    frontier_rows = []
    largest_cdf_tail_bound = 0.0
    largest_pmf_norm_error = 0.0
    for theta in (0.0, 0.25, 0.5, 0.75, 0.9):
        for r in range(-5, 13):
            a = q ** (r - theta)
            p = occupancy_probabilities(a, 12)
            cdf, tail_bound = limiting_maximum_cdf(q, theta, r)
            largest_cdf_tail_bound = max(largest_cdf_tail_bound, tail_bound)
            frontier_rows.append({
                "theta": theta, "r": r, "a_r": a,
                "mean_Z": occupancy_mean(a), "P_Z_0": p[0], "P_Z_1": p[1],
                "P_Z_ge_2": max(0.0, 1.0 - p[0] - p[1]),
                "maximum_CDF": cdf,
                "CDF_omitted_log_tail_bound": tail_bound,
            })
            # Resolve a large enough finite support to test the stable law.
            support = max(80, math.ceil(2 * a + 30))
            full_p = occupancy_probabilities(a, support)
            error = abs(float(np.sum(full_p)) - 1)
            largest_pmf_norm_error = max(largest_pmf_norm_error, error)
            assert error < 2e-12
            direct_mean = float(np.dot(np.arange(support + 1), full_p))
            assert abs(direct_mean - occupancy_mean(a)) < 2e-11 * max(a, 1)
    write_csv(data / "frontier_laws.csv", frontier_rows)

    count_rows = []
    for theta in np.linspace(0, 1, 257):
        mean, variance = limiting_occupied_count(q, float(theta))
        count_rows.append({"theta": theta, "occupied_count_limit_mean": mean,
                           "occupied_count_limit_variance": variance,
                           "mean_minus_theta": mean - theta})
    write_csv(data / "occupied_count_phase.csv", count_rows)
    mean_integral, mean_integral_error = quad(lambda x: limiting_occupied_count(q, x)[0],
                                            0, 1, epsabs=3e-12, epsrel=3e-12)
    var_integral, var_integral_error = quad(lambda x: limiting_occupied_count(q, x)[1],
                                          0, 1, epsabs=3e-12, epsrel=3e-12)
    expected_mean_integral = -math.log(2) / -math.log(q)
    expected_var_integral = (2 * math.log(2) - 1) / -math.log(q)
    assert abs(mean_integral - expected_mean_integral) < 2e-11
    assert abs(var_integral - expected_var_integral) < 2e-11
    c_l1, c_l1_tail = l1_constant(q)
    l1_rows = finite_l1_checks(q, logmu, c_l1, data)
    maximum_comparison = finite_maximum_checks(q, logmu, saddles, data)
    make_figures(q, stats, rows, figures)

    checks = {
        **exact,
        "floating_point": "IEEE 754 float64",
        "largest_floating_m": args.max_m,
        "max_exact_moment_relative_error": max_exact_moment_relative_error,
        "max_raw_probability_normalization_defect": stats["max_raw_probability_normalization_defect"],
        "max_absolute_saddle_equation_residual": max(abs(x["residual"]) for x in saddles.values()),
        "max_saddle_omitted_tail_bound": max(x["tail_bound"] for x in saddles.values()),
        "max_frontier_CDF_omitted_log_tail_bound": largest_cdf_tail_bound,
        "max_frontier_Z_probability_normalization_error": largest_pmf_norm_error,
        "finite_maximum_maximum_CDF_errors_on_s_minus3_to5": maximum_comparison,
        "occupied_count_phase_mean_integral": mean_integral,
        "occupied_count_phase_mean_integral_prediction": expected_mean_integral,
        "occupied_count_phase_mean_quadrature_error_estimate": mean_integral_error,
        "occupied_count_phase_variance_integral": var_integral,
        "occupied_count_phase_variance_integral_prediction": expected_var_integral,
        "occupied_count_phase_variance_quadrature_error_estimate": var_integral_error,
        "l1_constant": c_l1, "l1_constant_omitted_tail_bound": c_l1_tail,
        "l1_finite_comparisons": l1_rows,
        "python": platform.python_version(), "numpy": np.__version__,
        "scipy": scipy.__version__, "matplotlib": matplotlib.__version__,
        "numerical_checks_are_not_proofs": True,
    }
    (data / "verification_summary.json").write_text(
        json.dumps(checks, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    selected = [row for row in rows if row["m"] in (1, 4, 16, 64, 256, 1024, args.max_m)]
    lines = [
        "DETERMINISTIC NUMERICAL COMPANION: GEOMETRIC OCCUPANCY",
        "",
        f"Parameters: q={q_exact}; exact checks m=0..{args.exact_max}; float m=1..{args.max_m}.",
        "Reproduce: python verify_occupancy.py",
        "No Monte Carlo is used. These computations are evidence, not proofs.",
        "",
        "All exact Fraction assertions passed: moment-derived marginal sums;",
        "positivity; P(K0=0)=q^(2m); a direct two-head coefficient formula;",
        "conditional self-similarity; covariance; and monotone finite maximum CDFs.",
        "",
        "Numerical error diagnostics:",
        f"  Maximum exact-vs-float moment relative error: {max_exact_moment_relative_error:.4e}",
        f"  Maximum raw marginal normalization defect: {checks['max_raw_probability_normalization_defect']:.4e}",
        f"  Maximum absolute exact-saddle residual: {checks['max_absolute_saddle_equation_residual']:.4e}",
        f"  Maximum saddle omitted-tail bound: {checks['max_saddle_omitted_tail_bound']:.4e}",
        f"  Maximum frontier CDF omitted-log-tail bound: {largest_cdf_tail_bound:.4e}",
        f"  Maximum Z-law normalization defect: {largest_pmf_norm_error:.4e}",
        "  These tail bounds do not include floating-point roundoff or quadrature error.",
        "",
        "m, E(K0)/m, E(K1)/m, Var(K0)/m, Var(K1)/m, Cov(K0,K1)/m, t_m, theta_m",
    ]
    for row in selected:
        lines.append(
            f"{row['m']:4d}, {row['mean_K0_over_m']:.12f}, {row['mean_K1_over_m']:.12f}, "
            f"{row['var_K0_over_m']:.12f}, {row['var_K1_over_m']:.12f}, "
            f"{row['cov_K0_K1_over_m']:.12f}, {row['saddle_t']:.12f}, {row['frontier_theta']:.12f}")
    lines += [
        "",
        "Maximum finite-vs-phase-limit last-site CDF difference on s=-3..5:",
        *[f"  m={m}: {error:.12g}" for m, error in maximum_comparison.items()],
        "",
        f"Occupied-count phase mean integral: {mean_integral:.15f}; prediction {expected_mean_integral:.15f}.",
        f"Occupied-count phase variance integral: {var_integral:.15f}; prediction {expected_var_integral:.15f}.",
        f"Gaussian l1 mean constant: {c_l1:.15f}; omitted-tail bound <= {c_l1_tail:.4e}.",
        "Finite sqrt(m)*E||K/m-c||_1 values (omitted tail below 1e-11):",
        *[f"  m={row['m']}: {row['sqrt_m_expected_l1_partial_sum']:.12f}"
          for row in l1_rows],
        "Finite occupied-count means and variances:",
        *[f"  m={row['m']}: mean={row['occupied_count_mean']:.12f}, "
          f"variance={row['occupied_count_variance']:.12f}; "
          f"phase predictions={row['occupied_count_phase_mean_prediction']:.12f}, "
          f"{row['occupied_count_phase_variance_prediction']:.12f}"
          for row in selected if row['m'] >= 16],
        "",
        "Files:",
        "  figures/occupancy_convergence.pdf: exact-recursion mean, variance, covariance.",
        "  figures/frontier_limits.pdf: phase-dependent maximum CDF and frontier PMF.",
        "  Matching PNG previews and all CSV inputs are also included.",
        "  data/verification_summary.json records checks and runtime library versions.",
        "",
        "The saddle is the numerical root of the exact infinite-sum equation;",
        "it is not replaced by 2m. The finite maximum calculation uses finite",
        "head-product coefficients divided by infinite-product coefficients.",
        "Frontier-limit illustrations are labelled as limiting distributions.",
    ]
    (output / "numeric_notes.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines[:22]))
    print(f"Wrote deterministic data and two PDF figures to {output}")


if __name__ == "__main__":
    main()
