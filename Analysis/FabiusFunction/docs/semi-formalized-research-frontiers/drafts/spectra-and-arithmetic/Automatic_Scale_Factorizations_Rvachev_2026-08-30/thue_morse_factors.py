#!/usr/bin/env python3
"""Numerical experiments for Thue--Morse scale factorizations of the Rvachev law.

The Rvachev up law is the distribution of

    X = sum_{n>=1} U_n,   U_n ~ Uniform[-2^{-n}, 2^{-n}],

with independent summands.  We split the indices according to the two signs of the
Prouhet--Thue--Morse sequence e_m=(-1)^{s_2(m)} and study

    X_+ = sum_{e_{n-1}=+1} U_n,   X_- = sum_{e_{n-1}=-1} U_n.

This script verifies the exact product, q-Mahler, cumulant, zero-multiplicity, and
Mellin identities in the accompanying report.  It also creates reproducible tables
and figures illustrating the density factorization and the quadratic logarithmic
Fourier/Laplace envelopes.  The numerical experiments are evidence only; all results
labelled as theorems in the report are proved analytically there.

Run from this directory with

    python3 thue_morse_factors.py

Outputs are written to ./data and ./figures.  No network access is required.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Iterable, Literal

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
from scipy.ndimage import gaussian_filter1d

Sign = Literal[1, -1]


def thue_morse_sign(n: int) -> int:
    """Return e_n=(-1)^{s_2(n)} using parity of the binary digit sum."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


def selected(n: int, sign: Sign) -> bool:
    """Whether dyadic scale n>=1 belongs to the + or - Thue--Morse factor."""
    if n < 1:
        raise ValueError("scale index n must be at least 1")
    return thue_morse_sign(n - 1) == sign


def thue_morse_series(q: mp.mpf | mp.mpc, terms: int = 500) -> mp.mpf | mp.mpc:
    """Compute E(q)=sum e_n q^n.  For |q|<1 this equals prod_j(1-q^(2^j))."""
    total = mp.mpf("0")
    power = mp.mpf("1")
    for n in range(terms):
        total += thue_morse_sign(n) * power
        power *= q
    return total


def thue_morse_product(q: mp.mpf | mp.mpc, tolerance: mp.mpf | None = None) -> mp.mpf | mp.mpc:
    """Compute E(q) by its lacunary product, stopping after factors are negligible."""
    if abs(q) >= 1:
        raise ValueError("product is evaluated only for |q|<1")
    if tolerance is None:
        tolerance = mp.mpf(10) ** (-(mp.mp.dps - 10))
    product = mp.mpf("1")
    exponent = 1
    while abs(q) ** exponent > tolerance:
        product *= 1 - q**exponent
        exponent *= 2
    return product


def support_radius(sign: Sign, q: mp.mpf = mp.mpf("0.5")) -> mp.mpf:
    """Radius sum_{selected n} q^n = q/2*(1/(1-q)+/-E(q))."""
    return q / 2 * (1 / (1 - q) + sign * thue_morse_product(q))


def sinc_mp(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Entire normalized sinc."""
    return mp.mpf("1") if z == 0 else mp.sin(z) / z


def phi(z: mp.mpf | mp.mpc, sign: Sign | None, q: mp.mpf = mp.mpf("0.5"), terms: int = 180):
    """Truncated characteristic product.

    sign=None gives the full geometric product; sign=+1/-1 gives the corresponding
    Thue--Morse subproduct.  Here the scale at index n is q^n.
    """
    product = mp.mpf("1")
    for n in range(1, terms + 1):
        if sign is None or selected(n, sign):
            product *= sinc_mp(z * q**n)
    return product


def phi_logabs(x: float, sign: Sign | None, terms: int = 120) -> float:
    """Stable real log absolute characteristic product; -inf at exact zeros."""
    total = 0.0
    for n in range(1, terms + 1):
        if sign is None or selected(n, sign):
            y = x * (2.0 ** -n)
            if y == 0.0:
                continue
            value = abs(math.sin(y) / y)
            if value == 0.0:
                return -math.inf
            total += math.log(value)
    return total


def log_sinhc(x: mp.mpf) -> mp.mpf:
    """Stable h(x)=log(sinh(x)/x), including very large positive x."""
    x = abs(x)
    if x == 0:
        return mp.mpf("0")
    if x > 30:
        return x - mp.log(2 * x) + mp.log1p(-mp.e ** (-2 * x))
    return mp.log(mp.sinh(x) / x)


def log_mgf(t: mp.mpf, sign: Sign, terms: int = 300) -> mp.mpf:
    """K_+(t) or K_-(t) as a convergent sum of log-sinhc terms."""
    total = mp.mpf("0")
    for n in range(1, terms + 1):
        if selected(n, sign):
            total += log_sinhc(t * mp.power(2, -n))
    return total


def deficit_log_laplace(t: mp.mpf, sign: Sign, terms: int = 300) -> mp.mpf:
    """Log E exp(-t D_sign), D_sign=R_sign-X_sign>=0.

    If U_n is uniform on [-2^-n,2^-n], then 2^-n-U_n is uniform on
    [0,2^(1-n)].  The factor is (1-exp(-b*t))/(b*t), evaluated stably.
    """
    total = mp.mpf("0")
    for n in range(1, terms + 1):
        if not selected(n, sign):
            continue
        y = t * mp.power(2, 1 - n)
        if y < mp.mpf("1e-8"):
            # log((1-e^-y)/y) = -y/2 + y^2/24 - y^4/2880 + ...
            total += -y / 2 + y**2 / 24 - y**4 / 2880
        else:
            total += mp.log(-mp.expm1(-y) / y)
    return total


def cumulant(order: int, sign: Sign, q: mp.mpf = mp.mpf("0.5")) -> mp.mpf:
    """Exact even cumulant from Bernoulli numbers and the Thue--Morse q-product."""
    if order < 1:
        raise ValueError("order must be positive")
    if order & 1:
        return mp.mpf("0")
    m = order // 2
    q2m = q**order
    scale_sum = q2m / 2 * (1 / (1 - q2m) + sign * thue_morse_product(q2m))
    return mp.power(2, 2 * m - 1) * mp.bernpoly(2 * m, 0) / m * scale_sum


def moments_from_cumulants(max_order: int, sign: Sign) -> list[mp.mpf]:
    """Convert cumulants to raw moments using the complete Bell recurrence."""
    kappas = [mp.mpf("0")] + [cumulant(n, sign) for n in range(1, max_order + 1)]
    moments = [mp.mpf("1")] + [mp.mpf("0")] * max_order
    for n in range(1, max_order + 1):
        moments[n] = mp.fsum(
            mp.binomial(n - 1, k - 1) * kappas[k] * moments[n - k]
            for k in range(1, n + 1)
        )
    return moments


def prefix_sum(N: int) -> int:
    """S_N=sum_{m=0}^{N-1} e_m."""
    return sum(thue_morse_sign(m) for m in range(N))


def zero_multiplicity(k: int, sign: Sign) -> int:
    """Multiplicity at z=2*pi*k in phi_sign."""
    if k == 0:
        raise ValueError("k must be nonzero")
    v2 = 0
    a = abs(k)
    while a % 2 == 0:
        v2 += 1
        a //= 2
    N = 1 + v2
    return (N + sign * prefix_sum(N)) // 2


def phi_q(z: mp.mpc, q: mp.mpc, sign: Sign, terms: int = 140) -> mp.mpc:
    """General-q subproduct Phi_sign(z;q)=prod_{m>=0}sinc(z q^(m+1))^selector."""
    result = mp.mpc(1)
    for m in range(terms):
        if thue_morse_sign(m) == sign:
            result *= sinc_mp(z * q ** (m + 1))
    return result


def mellin_h_numeric(s: mp.mpc) -> mp.mpc:
    """Numerically integrate M[h](s), h(x)=log(sinh x/x), over (0,infinity)."""
    f = lambda x: log_sinhc(x) * x ** (s - 1)
    return mp.quad(f, [0, 1, mp.inf])


def theoretical_mellin_h(s: mp.mpc) -> mp.mpc:
    return -mp.power(2, -s) * mp.gamma(s) * mp.zeta(s + 1)


def write_csv(path: Path, rows: Iterable[dict[str, object]]) -> None:
    rows = list(rows)
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def simulate_densities(figures: Path, data: Path, samples: int, terms: int, seed: int) -> None:
    """Monte Carlo illustration of u_+, u_-, and their convolution.

    The exact convolution identity follows from characteristic functions; this plot is only
    a visual check.  Samples are accumulated in moderate chunks to keep memory bounded.
    """
    rng = np.random.default_rng(seed)
    x_plus = np.zeros(samples)
    x_minus = np.zeros(samples)
    for n in range(1, terms + 1):
        contribution = rng.uniform(-2.0**-n, 2.0**-n, size=samples)
        if selected(n, 1):
            x_plus += contribution
        else:
            x_minus += contribution
    x_full = x_plus + x_minus

    edges = np.linspace(-1.0, 1.0, 1601)
    centers = (edges[:-1] + edges[1:]) / 2
    width = edges[1] - edges[0]
    hp, _ = np.histogram(x_plus, bins=edges, density=True)
    hm, _ = np.histogram(x_minus, bins=edges, density=True)
    hf, _ = np.histogram(x_full, bins=edges, density=True)
    # A small fixed-bin Gaussian smoother suppresses Monte Carlo grain without changing the
    # support scale or the visible qualitative comparison.
    hp = gaussian_filter1d(hp, 2.0)
    hm = gaussian_filter1d(hm, 2.0)
    hf = gaussian_filter1d(hf, 2.0)

    rows = [
        {"x": f"{x:.9g}", "u_plus": f"{a:.9g}", "u_minus": f"{b:.9g}", "up": f"{c:.9g}"}
        for x, a, b, c in zip(centers, hp, hm, hf)
    ]
    write_csv(data / "density_histograms.csv", rows)

    plt.figure(figsize=(8.2, 4.9))
    plt.plot(centers, hp, label=r"$u_+$")
    plt.plot(centers, hm, label=r"$u_-$")
    plt.plot(centers, hf, label=r"$u_+*u_-=\mathrm{up}$")
    plt.xlabel("x")
    plt.ylabel("estimated density")
    plt.title("Thue–Morse scale factors and their Rvachev convolution")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures / "factor_densities.pdf")
    plt.savefig(figures / "factor_densities.png", dpi=180)
    plt.close()

    # Convolution of the two estimated histograms, for a separate quantitative comparison.
    convolution = np.convolve(hp, hm, mode="full") * width
    conv_x = np.linspace(2 * centers[0], 2 * centers[-1], convolution.size)
    interp = np.interp(centers, conv_x, convolution)
    l1_error = float(np.sum(np.abs(interp - hf)) * width)
    (data / "density_convolution_check.txt").write_text(
        f"Histogram-based L1 discrepancy: {l1_error:.12g}\n"
        "This number contains sampling, binning, smoothing, and truncation error.\n",
        encoding="utf-8",
    )


def create_decay_figure(figures: Path, data: Path) -> dict[str, float]:
    """Illustrate the quadratic-log Fourier envelope at nonresonant sample points."""
    logs = np.linspace(3.0, 18.0, 260)
    # The irrational additive offset avoids systematically landing exactly on dyadic zeros.
    xs = np.exp(logs) + math.sqrt(2.0)
    rows: list[dict[str, object]] = []
    values: dict[str, list[float]] = {"plus": [], "minus": [], "full": []}
    for L, x in zip(logs, xs):
        for name, sign in (("plus", 1), ("minus", -1), ("full", None)):
            la = phi_logabs(float(x), sign)
            ratio = -la / (math.log(float(x)) ** 2)
            values[name].append(ratio)
        rows.append(
            {
                "log_x": f"{L:.12g}",
                "x": f"{x:.12g}",
                "plus_ratio": f"{values['plus'][-1]:.12g}",
                "minus_ratio": f"{values['minus'][-1]:.12g}",
                "full_ratio": f"{values['full'][-1]:.12g}",
            }
        )
    write_csv(data / "fourier_decay.csv", rows)

    predicted_factor = 1.0 / (4.0 * math.log(2.0))
    predicted_full = 1.0 / (2.0 * math.log(2.0))
    plt.figure(figsize=(8.2, 4.9))
    plt.plot(logs, values["plus"], label=r"$-\log|\phi_+|/(\log x)^2$")
    plt.plot(logs, values["minus"], label=r"$-\log|\phi_-|/(\log x)^2$")
    plt.plot(logs, values["full"], label=r"$-\log|\phi|/(\log x)^2$")
    plt.axhline(predicted_factor, linestyle="--", label=r"$1/(4\log 2)$")
    plt.axhline(predicted_full, linestyle=":", label=r"$1/(2\log 2)$")
    plt.xlabel(r"$\log x$")
    plt.ylabel("normalized log modulus")
    plt.title("Quadratic-log Fourier decay along a nonresonant ray")
    plt.ylim(bottom=0)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(figures / "fourier_decay.pdf")
    plt.savefig(figures / "fourier_decay.png", dpi=180)
    plt.close()
    return {"factor_prediction": predicted_factor, "full_prediction": predicted_full}


def create_laplace_figure(figures: Path, data: Path) -> dict[str, float]:
    """Illustrate the support-reduced log-MGF and deficit Laplace asymptotics."""
    log_ts = np.linspace(3.0, 28.0, 180)
    rows: list[dict[str, object]] = []
    ratio_plus: list[float] = []
    ratio_minus: list[float] = []
    laplace_plus: list[float] = []
    laplace_minus: list[float] = []
    rp = support_radius(1)
    rm = support_radius(-1)
    for L in log_ts:
        t = mp.e ** mp.mpf(str(L))
        kp = log_mgf(t, 1)
        km = log_mgf(t, -1)
        lp = deficit_log_laplace(t, 1)
        lm = deficit_log_laplace(t, -1)
        denominator = mp.log(t) ** 2
        ratio_plus.append(float(-(kp - rp * t) / denominator))
        ratio_minus.append(float(-(km - rm * t) / denominator))
        laplace_plus.append(float(-lp / denominator))
        laplace_minus.append(float(-lm / denominator))
        rows.append(
            {
                "log_t": f"{L:.12g}",
                "mgf_plus_ratio": f"{ratio_plus[-1]:.12g}",
                "mgf_minus_ratio": f"{ratio_minus[-1]:.12g}",
                "laplace_plus_ratio": f"{laplace_plus[-1]:.12g}",
                "laplace_minus_ratio": f"{laplace_minus[-1]:.12g}",
            }
        )
    write_csv(data / "laplace_mgf_asymptotics.csv", rows)
    predicted = 1.0 / (4.0 * math.log(2.0))
    plt.figure(figsize=(8.2, 4.9))
    plt.plot(log_ts, ratio_plus, label=r"$-(K_+(t)-R_+t)/(\log t)^2$")
    plt.plot(log_ts, ratio_minus, label=r"$-(K_-(t)-R_-t)/(\log t)^2$")
    plt.plot(log_ts, laplace_plus, linestyle="--", label=r"$-\log L_+(t)/(\log t)^2$")
    plt.plot(log_ts, laplace_minus, linestyle="--", label=r"$-\log L_-(t)/(\log t)^2$")
    plt.axhline(predicted, linestyle=":", label=r"$1/(4\log 2)$")
    plt.xlabel(r"$\log t$")
    plt.ylabel("normalized logarithm")
    plt.title("Universal half-density edge coefficient")
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(figures / "laplace_mgf_asymptotics.pdf")
    plt.savefig(figures / "laplace_mgf_asymptotics.png", dpi=180)
    plt.close()
    return {"prediction": predicted}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=800_000, help="Monte Carlo sample count")
    parser.add_argument("--terms", type=int, default=45, help="random-series truncation")
    parser.add_argument("--seed", type=int, default=20260830, help="deterministic RNG seed")
    args = parser.parse_args()

    mp.mp.dps = 80
    root = Path(__file__).resolve().parent
    figures = root / "figures"
    data = root / "data"
    figures.mkdir(exist_ok=True)
    data.mkdir(exist_ok=True)

    Ehalf_series = thue_morse_series(mp.mpf("0.5"), 600)
    Ehalf_product = thue_morse_product(mp.mpf("0.5"))
    rplus = support_radius(1)
    rminus = support_radius(-1)

    cumulant_rows = []
    moments = {1: moments_from_cumulants(12, 1), -1: moments_from_cumulants(12, -1)}
    for order in range(2, 13, 2):
        cumulant_rows.append(
            {
                "order": order,
                "kappa_plus": mp.nstr(cumulant(order, 1), 32),
                "kappa_minus": mp.nstr(cumulant(order, -1), 32),
                "moment_plus": mp.nstr(moments[1][order], 32),
                "moment_minus": mp.nstr(moments[-1][order], 32),
            }
        )
    write_csv(data / "cumulants_and_moments.csv", cumulant_rows)

    # Product factorization and q-Mahler checks at generic complex points.
    z = mp.mpc("1.234", "0.271")
    q = mp.mpc("0.37", "0.09")
    product_residual = abs(phi(z, 1) * phi(z, -1) - phi(z, None))
    qmahler_plus = abs(phi_q(z, q, 1) - phi_q(z / q, q**2, 1) * phi_q(z, q**2, -1))
    qmahler_minus = abs(phi_q(z, q, -1) - phi_q(z / q, q**2, -1) * phi_q(z, q**2, 1))

    # Mellin identity at two points in the fundamental strip -2<Re(s)<-1.
    mellin_checks = []
    for s in (mp.mpf("-1.5"), mp.mpc("-1.4", "0.3")):
        numeric = mellin_h_numeric(s)
        theory = theoretical_mellin_h(s)
        mellin_checks.append(
            {
                "s": str(s),
                "numeric": mp.nstr(numeric, 32),
                "theory": mp.nstr(theory, 32),
                "absolute_error": mp.nstr(abs(numeric - theory), 8),
            }
        )
    write_csv(data / "mellin_checks.csv", mellin_checks)

    zero_rows = []
    for k in range(1, 33):
        zero_rows.append(
            {
                "k": k,
                "v2_k": (abs(k) & -abs(k)).bit_length() - 1,
                "multiplicity_plus": zero_multiplicity(k, 1),
                "multiplicity_minus": zero_multiplicity(k, -1),
                "multiplicity_total": zero_multiplicity(k, 1) + zero_multiplicity(k, -1),
            }
        )
    write_csv(data / "zero_multiplicities.csv", zero_rows)

    decay_summary = create_decay_figure(figures, data)
    laplace_summary = create_laplace_figure(figures, data)
    simulate_densities(figures, data, args.samples, args.terms, args.seed)

    summary = {
        "precision_decimal_digits": mp.mp.dps,
        "thue_morse_E_half_series": mp.nstr(Ehalf_series, 60),
        "thue_morse_E_half_product": mp.nstr(Ehalf_product, 60),
        "support_radius_plus": mp.nstr(rplus, 60),
        "support_radius_minus": mp.nstr(rminus, 60),
        "support_radius_sum": mp.nstr(rplus + rminus, 60),
        "factorization_absolute_residual": mp.nstr(product_residual, 12),
        "q_mahler_plus_absolute_residual": mp.nstr(qmahler_plus, 12),
        "q_mahler_minus_absolute_residual": mp.nstr(qmahler_minus, 12),
        "predicted_fourier_coefficients": decay_summary,
        "predicted_edge_coefficient": laplace_summary,
        "random_seed": args.seed,
        "monte_carlo_samples": args.samples,
        "random_series_terms": args.terms,
    }
    (data / "numerical_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
