#!/usr/bin/env python3
"""Reproducible experiments for the dyadic Fabius--Rvachev chaos report.

This script verifies and visualizes the exact identities developed in
``fabius_dyadic_chaos_frontiers.tex``.  It deliberately keeps the mathematical
normalization visible:

    V_j ~ Uniform[-1,1], independent,
    X   = sum_{j>=1} 2^{-j} V_j,
    M(t)= E exp(t X) = product_{j>=1} sinh(t/2^j)/(t/2^j).

For the exponential observable exp(tX), the local Hoeffding variance ratio and
its Bernoulli activation probability are

    r(x) = m(2*x)/m(x)^2 - 1,
    p(x) = r(x)/(1+r(x)),

with r(0)=p(0)=0.  Away from zero these are respectively
``x*coth(x)-1`` and ``1-tanh(x)/x``.

The code performs only deterministic high-precision calculations; no Monte
Carlo sampling is needed.  Every truncation uses an explicit geometric tail
bound, and the output files record the chosen precision and truncation depth.

Outputs
-------
* data/effective_dimension.csv
* data/fourier_coefficients.csv
* data/chaos_order_distributions.csv
* data/phase_limit_convergence.csv
* data/qbinomial_asymptotics.csv
* data/legendre_parseval.csv
* data/legendre_degree_marks.csv
* data/polynomial_top_energy.csv
* data/no_active_atom.csv
* data/numerical_summary.txt
* figures/*.pdf and figures/*.png

The script is compatible with Python 3.11+ and uses mpmath, numpy, scipy, and
matplotlib.  All formulas are implemented independently of the LaTeX source so
that transcription errors are more likely to be detected.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import spherical_in


MP_DPS = 80
mp.mp.dps = MP_DPS
LOG2 = mp.log(2)

# Matplotlib otherwise emits Type-3 glyphs in PDF output.  TrueType embedding
# keeps the vector figures searchable, scalable, and suitable for inclusion in
# the report without importing Type-3 fonts into the final document.
plt.rcParams["pdf.fonttype"] = 42
plt.rcParams["ps.fonttype"] = 42


def mp_sinhc(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return sinh(x)/x with the removable value 1 at x=0."""
    if x == 0:
        return mp.mpf(1)
    return mp.sinh(x) / x


def local_r(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return the totalized local energy ``m(2*x)/m(x)^2 - 1``.

    This equals ``x*coth(x)-1`` away from zero and has value zero at the
    origin.  A short Taylor expansion both supplies that removable value and
    avoids catastrophic cancellation nearby.
    """
    ax = abs(x)
    if ax < mp.mpf("1e-8"):
        x2 = x * x
        return (
            x2 / 3
            - x2**2 / 45
            + 2 * x2**3 / 945
            - x2**4 / 4725
            + 2 * x2**5 / 93555
        )
    return x / mp.tanh(x) - 1


def local_p(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return the active probability, totalized by ``p(0)=0``.

    Away from zero this is ``1-tanh(x)/x``.
    """
    ax = abs(x)
    if ax < mp.mpf("1e-8"):
        x2 = x * x
        return (
            x2 / 3
            - 2 * x2**2 / 15
            + 17 * x2**3 / 315
            - 62 * x2**4 / 2835
            + 1382 * x2**5 / 155925
        )
    return 1 - mp.tanh(x) / x


def choose_jmax(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-40")) -> int:
    """Choose J so sum_{j>J} p(t/2^j) <= tail_tol.

    The global inequality p(x) <= x^2/3 gives
        sum_{j>J} p(t/2^j) <= t^2/(9*4^J).
    """
    t = abs(mp.mpf(t))
    if t == 0:
        return 1
    ratio = t * t / (9 * tail_tol)
    if ratio <= 1:
        return 1
    return max(1, int(mp.ceil(mp.log(ratio, 4))))


def log_mgf(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-50")) -> mp.mpf:
    """High-precision log M(t), with a certified power-tail estimate."""
    t = mp.mpf(t)
    jmax = choose_jmax(t, tail_tol)
    total = mp.mpf(0)
    for j in range(1, jmax + 1):
        x = t / (2**j)
        total += mp.log(mp_sinhc(x))
    # The omitted log(sinhc x) tail is positive and <= sum x^2/6 for real x.
    # Its bound is t^2/(18*4^J), below tail_tol/2 by the chosen depth.
    return total


def mgf(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-50")) -> mp.mpf:
    return mp.exp(log_mgf(t, tail_tol))


def effective_dimension(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-45")) -> tuple[mp.mpf, int, mp.mpf]:
    """Return mu(t)=sum_j p(t/2^j), J, and the geometric tail bound."""
    t = abs(mp.mpf(t))
    jmax = choose_jmax(t, tail_tol)
    value = mp.fsum(local_p(t / (2**j)) for j in range(1, jmax + 1))
    tail_bound = t * t / (9 * mp.power(4, jmax))
    return value, jmax, tail_bound


def bernoulli_probabilities(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-30")) -> tuple[list[float], int, float]:
    """Finite list p_j with an explicit omitted-mean bound."""
    t = abs(mp.mpf(t))
    jmax = choose_jmax(t, tail_tol)
    probs = [float(local_p(t / (2**j))) for j in range(1, jmax + 1)]
    bound = float(t * t / (9 * mp.power(4, jmax)))
    return probs, jmax, bound


def poisson_binomial_pmf(probs: Sequence[float]) -> np.ndarray:
    """Stable O(n^2) convolution for a Poisson--binomial law."""
    pmf = np.array([1.0], dtype=float)
    for p in probs:
        nxt = np.zeros(len(pmf) + 1, dtype=float)
        nxt[:-1] += pmf * (1.0 - p)
        nxt[1:] += pmf * p
        pmf = nxt
    # Remove tiny roundoff drift without changing meaningful digits.
    pmf[pmf < 0] = 0.0
    pmf /= pmf.sum()
    return pmf


def conditioned_chaos_order_pmf(t: mp.mpf, tail_tol: mp.mpf = mp.mpf("1e-30")) -> tuple[np.ndarray, int, float]:
    """ANOVA order weights P(K_t=k | K_t>0), k>=1."""
    probs, jmax, bound = bernoulli_probabilities(t, tail_tol)
    pmf = poisson_binomial_pmf(probs)
    if 1.0 - pmf[0] <= 0:
        raise RuntimeError("nonempty chaos mass underflowed")
    cond = pmf.copy()
    cond[0] = 0.0
    cond /= cond.sum()
    return cond, jmax, bound


def elementary_symmetric(values: Sequence[mp.mpf], kmax: int) -> list[mp.mpf]:
    """e_0,...,e_kmax by descending-order dynamic programming."""
    e = [mp.mpf(0)] * (kmax + 1)
    e[0] = mp.mpf(1)
    for x in values:
        for k in range(kmax, 0, -1):
            e[k] += x * e[k - 1]
    return e


def qpochhammer(q: mp.mpf, k: int) -> mp.mpf:
    result = mp.mpf(1)
    for j in range(1, k + 1):
        result *= 1 - q**j
    return result


def leading_Ak(t: mp.mpf, k: int) -> mp.mpf:
    """Leading q-binomial term for A_k(t) in the dyadic law."""
    q = mp.mpf(1) / 4
    return (
        (t ** (2 * k))
        / (3**k)
        * q ** (k * (k + 1) / 2)
        / qpochhammer(q, k)
    )


def corrected_Ak(t: mp.mpf, k: int) -> mp.mpf:
    """Leading plus first correction for A_k(t)."""
    q = mp.mpf(1) / 4
    a = mp.mpf(1) / 3
    b = -mp.mpf(1) / 45
    e1 = q / (1 - q)
    ek = q ** (k * (k + 1) / 2) / qpochhammer(q, k)
    ek1 = q ** ((k + 1) * (k + 2) / 2) / qpochhammer(q, k + 1)
    return a**k * t ** (2 * k) * ek + b * a ** (k - 1) * t ** (2 * k + 2) * (
        e1 * ek - (k + 1) * ek1
    )


def exact_A_values(t: mp.mpf, kmax: int, tail_tol: mp.mpf = mp.mpf("1e-55")) -> tuple[list[mp.mpf], int]:
    jmax = choose_jmax(t, tail_tol)
    rs = [mp.mpf(local_r(t / (2**j))) for j in range(1, jmax + 1)]
    return elementary_symmetric(rs, kmax), jmax


def mellin_P(s: mp.mpc) -> mp.mpc:
    """Mellin transform of p on -2<Re(s)<0, analytically continued elsewhere."""
    return mp.power(2, 2 - s) * (1 - mp.power(2, 2 - s)) * mp.gamma(s - 1) * mp.zeta(s - 1)


def mellin_I(s: mp.mpc) -> mp.mpc:
    """Mellin transform of p': I(s)=-s P(s)."""
    return (
        mp.power(2, 2 - s)
        * (1 - mp.power(2, 2 - s))
        * mp.gamma(s + 1)
        * mp.zeta(s - 1)
        / (1 - s)
    )


def glaisher_constant() -> mp.mpf:
    """A = exp(1/12-zeta'(-1)), used only through this defining identity."""
    return mp.exp(mp.mpf(1) / 12 - mp.diff(mp.zeta, -1))


def q_mean_constant() -> mp.mpf:
    """Mean Fourier coefficient of Q(theta)."""
    A = glaisher_constant()
    return mp.mpf(11) / 6 + (mp.euler - 12 * mp.log(A)) / LOG2


def qhat(n: int) -> mp.mpc:
    """Fourier coefficient in Q(theta)=sum_n qhat(n)e^{2 pi i n theta}."""
    if n == 0:
        return mp.mpc(q_mean_constant())
    tau = 2 * mp.pi * n / LOG2
    return mellin_P(-1j * tau) / LOG2


def q_fourier(theta: mp.mpf, harmonics: int = 4) -> mp.mpf:
    value = mp.mpf(qhat(0).real)
    for n in range(1, harmonics + 1):
        value += 2 * mp.re(qhat(n) * mp.e ** (2j * mp.pi * n * theta))
    return value


def direct_Q(theta: mp.mpf, nscale: int = 35) -> tuple[mp.mpf, mp.mpf]:
    t = mp.power(2, nscale + theta)
    mu, _, tail = effective_dimension(t, mp.mpf("1e-55"))
    return mu - mp.log(t, 2), tail


def phase_centered_pmf(theta: float, nscale: int, tail_tol: mp.mpf = mp.mpf("1e-30")) -> tuple[np.ndarray, np.ndarray]:
    """Distribution of K_{2^(n+theta)}-n on its finite computed support."""
    t = mp.power(2, mp.mpf(nscale) + mp.mpf(theta))
    probs, _, _ = bernoulli_probabilities(t, tail_tol)
    pmf = poisson_binomial_pmf(probs)
    support = np.arange(len(pmf), dtype=int) - nscale
    return support, pmf


def tv_distance_on_integer_lattice(s1: np.ndarray, p1: np.ndarray, s2: np.ndarray, p2: np.ndarray) -> float:
    lo = int(min(s1.min(), s2.min()))
    hi = int(max(s1.max(), s2.max()))
    a = np.zeros(hi - lo + 1)
    b = np.zeros(hi - lo + 1)
    a[s1 - lo] = p1
    b[s2 - lo] = p2
    return 0.5 * float(np.abs(a - b).sum())


def modified_spherical_i(n: int, x: float) -> float:
    if x == 0.0:
        return 1.0 if n == 0 else 0.0
    return float(spherical_in(n, x))


def polynomial_top_energy(d: int) -> Fraction:
    """Exact order-d energy of X^d for dyadic weights."""
    # e_d(4^{-1},4^{-2},...) = 4^{-d(d+1)/2}/prod_{j=1}^d(1-4^{-j}).
    e = Fraction(1, 1)
    e *= Fraction(1, 4 ** (d * (d + 1) // 2))
    for j in range(1, d + 1):
        e /= Fraction(4**j - 1, 4**j)
    return Fraction(math.factorial(d) ** 2, 3**d) * e


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(header)
        writer.writerows(rows)


def save_figure(fig: plt.Figure, stem: Path) -> None:
    fig.tight_layout()
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.close(fig)


@dataclass
class ExperimentContext:
    root: Path

    @property
    def data(self) -> Path:
        return self.root / "data"

    @property
    def figures(self) -> Path:
        return self.root / "figures"


def run_effective_dimension(ctx: ExperimentContext) -> dict[str, mp.mpf]:
    rows = []
    thetas = np.linspace(0.0, 1.0, 257, endpoint=False)
    direct_centered = []
    first_harmonic_centered = []
    q0 = q_mean_constant()
    max_error = mp.mpf(0)
    for theta_float in thetas:
        theta = mp.mpf(str(theta_float))
        direct, tail = direct_Q(theta, nscale=35)
        fourier = q_fourier(theta, harmonics=4)
        first = q0 + 2 * mp.re(qhat(1) * mp.e ** (2j * mp.pi * theta))
        error = abs(direct - fourier)
        max_error = max(max_error, error)
        rows.append(
            [
                f"{theta_float:.12g}",
                mp.nstr(direct, 30),
                mp.nstr(fourier, 30),
                mp.nstr(first, 30),
                mp.nstr(error, 12),
                mp.nstr(tail, 12),
            ]
        )
        direct_centered.append(float(direct - q0))
        first_harmonic_centered.append(float(first - q0))
    write_csv(
        ctx.data / "effective_dimension.csv",
        ["theta", "Q_direct", "Q_fourier_4", "Q_first_harmonic", "abs_error", "tail_bound"],
        rows,
    )

    coeff_rows = []
    for n in range(0, 9):
        c = qhat(n)
        coeff_rows.append(
            [n, mp.nstr(c.real, 40), mp.nstr(c.imag, 40), mp.nstr(abs(c), 30)]
        )
    write_csv(
        ctx.data / "fourier_coefficients.csv",
        ["n", "real", "imag", "absolute_value"],
        coeff_rows,
    )

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(thetas, direct_centered, label="direct dyadic sum")
    ax.plot(thetas, first_harmonic_centered, linestyle="--", label="first Fourier harmonic")
    ax.set_xlabel(r"$\theta$")
    ax.set_ylabel(r"$Q(\theta)-\widehat Q(0)$")
    ax.set_title("Log-periodic fluctuation of the effective interaction order")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, ctx.figures / "periodic_effective_dimension")

    return {
        "q0": q0,
        "q1_abs": abs(qhat(1)),
        "q1_peak_amplitude": 2 * abs(qhat(1)),
        "max_Q_fourier_error": max_error,
    }


def run_chaos_distributions(ctx: ExperimentContext) -> dict[str, float]:
    t_values = [1.0, 4.0, 16.0, 64.0, 256.0]
    rows = []
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for t in t_values:
        cond, jmax, tail = conditioned_chaos_order_pmf(mp.mpf(t), mp.mpf("1e-28"))
        k = np.arange(len(cond))
        keep = cond > 1e-13
        ax.plot(k[keep] - math.log2(t), cond[keep], marker="o", markersize=3, label=f"t={t:g}")
        mu, _, _ = effective_dimension(mp.mpf(t))
        p0 = float(mgf(mp.mpf(t)) / mp_sinhc(mp.mpf(t)))
        for idx, prob in enumerate(cond):
            if prob > 1e-16:
                rows.append([t, idx, f"{prob:.17g}", jmax, f"{tail:.3e}", mp.nstr(mu, 20), f"{p0:.17g}"])
    write_csv(
        ctx.data / "chaos_order_distributions.csv",
        ["t", "order_k", "conditional_weight", "jmax", "omitted_mean_bound", "unconditioned_mean", "P_K_eq_0"],
        rows,
    )
    ax.set_xlabel(r"$k-\log_2 t$")
    ax.set_ylabel(r"$\mathrm{P}(K_t=k\mid K_t>0)$")
    ax.set_title("Centered ANOVA interaction-order distributions")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, ctx.figures / "chaos_order_distributions")

    theta = 0.37
    ref_support, ref_pmf = phase_centered_pmf(theta, 34, mp.mpf("1e-32"))
    tv_rows = []
    n_values = list(range(4, 25, 2))
    tv_values = []
    bounds = []
    for n in n_values:
        support, pmf = phase_centered_pmf(theta, n, mp.mpf("1e-32"))
        tv = tv_distance_on_integer_lattice(support, pmf, ref_support, ref_pmf)
        t = 2 ** (n + theta)
        bound = 2 / t + 2 / (2 ** (34 + theta))
        tv_values.append(tv)
        bounds.append(bound)
        tv_rows.append([theta, n, f"{t:.17g}", f"{tv:.17g}", f"{bound:.17g}"])
    write_csv(
        ctx.data / "phase_limit_convergence.csv",
        ["theta", "n", "t", "TV_to_n34_reference", "coupling_bound"],
        tv_rows,
    )
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.semilogy(n_values, tv_values, marker="o", label="computed total variation")
    ax.semilogy(n_values, bounds, linestyle="--", label="explicit coupling bound")
    ax.set_xlabel(r"$n$ in $t=2^{n+\theta}$")
    ax.set_ylabel("total variation distance")
    ax.set_title(r"Phase-law convergence at $\theta=0.37$")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, ctx.figures / "phase_limit_convergence")

    return {"phase_tv_n24": tv_values[-1], "phase_bound_n24": bounds[-1]}


def run_qbinomial(ctx: ExperimentContext) -> dict[str, mp.mpf]:
    rows = []
    t_values = [mp.mpf(2) ** (-j) for j in range(1, 10)]
    max_rel_corrected = mp.mpf(0)
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for k in range(1, 5):
        plot_t = []
        plot_err = []
        for t in t_values:
            exact, jmax = exact_A_values(t, 4)
            lead = leading_Ak(t, k)
            corr = corrected_Ak(t, k)
            rel_lead = abs(exact[k] / lead - 1)
            rel_corr = abs(exact[k] / corr - 1)
            max_rel_corrected = max(max_rel_corrected, rel_corr)
            rows.append(
                [
                    k,
                    mp.nstr(t, 20),
                    mp.nstr(exact[k], 35),
                    mp.nstr(lead, 35),
                    mp.nstr(corr, 35),
                    mp.nstr(rel_lead, 20),
                    mp.nstr(rel_corr, 20),
                    jmax,
                ]
            )
            plot_t.append(float(t))
            plot_err.append(float(rel_lead))
        ax.loglog(plot_t, plot_err, marker="o", label=f"k={k}")
    write_csv(
        ctx.data / "qbinomial_asymptotics.csv",
        ["k", "t", "A_k_exact", "leading_term", "first_corrected", "relative_error_leading", "relative_error_corrected", "jmax"],
        rows,
    )
    ax.set_xlabel(r"$t$")
    ax.set_ylabel("relative error of leading q-binomial term")
    ax.set_title("Small-parameter q-binomial asymptotics of chaos order energies")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, ctx.figures / "qbinomial_asymptotic_error")
    return {"max_relative_corrected_error_grid": max_rel_corrected}


def run_legendre(ctx: ExperimentContext) -> dict[str, float]:
    parseval_rows = []
    max_parseval_error = 0.0
    for x in [0.1, 0.5, 1.0, 2.0, 4.0]:
        for nmax in [4, 8, 16, 32, 64]:
            total = sum((2 * n + 1) * modified_spherical_i(n, x) ** 2 for n in range(nmax + 1))
            target = math.sinh(2 * x) / (2 * x)
            err = abs(total - target)
            max_parseval_error = max(max_parseval_error, err if nmax == 64 else 0.0)
            parseval_rows.append([x, nmax, f"{total:.17g}", f"{target:.17g}", f"{err:.17g}"])
    write_csv(
        ctx.data / "legendre_parseval.csv",
        ["x", "nmax", "partial_sum", "sinh_2x_over_2x", "absolute_error"],
        parseval_rows,
    )

    mark_rows = []
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for x in [0.5, 1.0, 2.0, 4.0]:
        m0 = math.sinh(x) / x
        denom = math.sinh(2 * x) / (2 * x) - m0 * m0
        ns = np.arange(1, 31)
        probs = np.array([(2 * n + 1) * modified_spherical_i(int(n), x) ** 2 / denom for n in ns])
        ax.semilogy(ns, probs, marker="o", markersize=3, label=f"x={x:g}")
        for n, prob in zip(ns, probs):
            mark_rows.append([x, int(n), f"{prob:.17g}"])
    write_csv(
        ctx.data / "legendre_degree_marks.csv",
        ["x", "degree_n", "conditional_probability_given_active"],
        mark_rows,
    )
    ax.set_xlabel("local Legendre degree n")
    ax.set_ylabel("conditional squared-coefficient mass")
    ax.set_title("Marked Legendre degree law at one active digit")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, ctx.figures / "legendre_degree_marks")
    return {"max_parseval_error_n64": max_parseval_error}


def run_polynomial_energy(ctx: ExperimentContext) -> dict[str, float]:
    rows = []
    ds = list(range(1, 16))
    vals = []
    for d in ds:
        value = polynomial_top_energy(d)
        vals.append(float(value))
        rows.append([d, value.numerator, value.denominator, f"{float(value):.17g}"])
    write_csv(
        ctx.data / "polynomial_top_energy.csv",
        ["degree_d", "numerator", "denominator", "decimal"],
        rows,
    )
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.semilogy(ds, vals, marker="o")
    ax.set_xlabel("polynomial degree d")
    ax.set_ylabel(r"exact order-$d$ ANOVA energy of $X^d$")
    ax.set_title("Sharp q-Pochhammer top-interaction energies for monomials")
    ax.grid(True, alpha=0.25)
    save_figure(fig, ctx.figures / "polynomial_top_energy")
    return {"top_energy_d10": float(polynomial_top_energy(10))}


def run_no_active_atom(ctx: ExperimentContext) -> dict[str, mp.mpf]:
    rows = []
    max_identity_error = mp.mpf(0)
    for t_int in [1, 2, 4, 8, 16, 32, 64, 128, 256]:
        t = mp.mpf(t_int)
        p0_product = mgf(t) / mp_sinhc(t)
        # G(-2t) is the negative Laplace transform of the [0,1] Fabius law.
        # Its product is evaluated independently here.
        jmax = choose_jmax(2 * t, mp.mpf("1e-50"))
        log_g = mp.fsum(
            mp.log((1 - mp.e ** (-(2 * t) / (2**j))) / ((2 * t) / (2**j)))
            for j in range(1, jmax + 1)
        )
        p0_laplace = 2 * t * mp.e**log_g / (1 - mp.e ** (-2 * t))
        error = abs(p0_product - p0_laplace)
        max_identity_error = max(max_identity_error, error)
        rows.append(
            [
                t_int,
                mp.nstr(p0_product, 40),
                mp.nstr(p0_laplace, 40),
                mp.nstr(error, 15),
                mp.nstr(mp.log(p0_product), 35),
                jmax,
            ]
        )
    write_csv(
        ctx.data / "no_active_atom.csv",
        ["t", "P_K_eq_0_product", "P_K_eq_0_negative_Laplace", "absolute_error", "log_P_K_eq_0", "jmax"],
        rows,
    )
    return {"max_no_active_identity_error": max_identity_error}


def write_summary(ctx: ExperimentContext, summaries: Sequence[dict[str, object]]) -> None:
    combined: dict[str, object] = {}
    for part in summaries:
        combined.update(part)
    lines = [
        "Dyadic Fabius--Rvachev chaos experiments",
        f"mpmath decimal precision: {MP_DPS}",
        "All probability-tail truncations use p(x)<=x^2/3.",
        "",
    ]
    for key in sorted(combined):
        value = combined[key]
        if isinstance(value, (mp.mpf, mp.mpc)):
            text = mp.nstr(value, 50)
        else:
            text = repr(value)
        lines.append(f"{key}: {text}")
    lines.extend(
        [
            "",
            "Key exact constants:",
            f"Glaisher A (definition exp(1/12-zeta'(-1))): {mp.nstr(glaisher_constant(), 50)}",
            f"mean Q coefficient: {mp.nstr(q_mean_constant(), 50)}",
            f"qhat(1): {mp.nstr(qhat(1), 50)}",
            f"2*abs(qhat(1)): {mp.nstr(2*abs(qhat(1)), 50)}",
        ]
    )
    (ctx.data / "numerical_summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="artifact root containing data/ and figures/",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    ctx = ExperimentContext(args.root.resolve())
    ctx.data.mkdir(parents=True, exist_ok=True)
    ctx.figures.mkdir(parents=True, exist_ok=True)

    summaries = [
        run_effective_dimension(ctx),
        run_chaos_distributions(ctx),
        run_qbinomial(ctx),
        run_legendre(ctx),
        run_polynomial_energy(ctx),
        run_no_active_atom(ctx),
    ]
    write_summary(ctx, summaries)
    print(f"Wrote data to {ctx.data}")
    print(f"Wrote figures to {ctx.figures}")


if __name__ == "__main__":
    main()
