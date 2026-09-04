#!/usr/bin/env python3
"""Reproducible experiments for the Rvachev atomic-function report.

The script audits formulas rather than replacing their proofs.  It generates every
figure and CSV table referenced by ``Atomic_Functions_Beyond_Dyadic_Expanded.tex``.
Only NumPy, Matplotlib, and mpmath are required.

Mathematical conventions
------------------------
For a > 1,

    Phi_a(t) = product_{j>=1} sinc(t a^{-j}),
    sinc(x) = sin(x)/x,

and h_a is the inverse Fourier transform of Phi_a.  In the separated regime a >= 2,
exact derivative thinning gives the spectral moments

    m_n = integral t^(2n)|Phi_a(t)|^2 dt / integral |Phi_a(t)|^2 dt
        = a^(n(n+2))/2^n.

The q-orthogonal polynomials used below are the monic scaled Stieltjes-Wigert
polynomials for q=a^{-2}, c=a/2.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

SEED = 20260828


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    """Return sin(x)/x with the removable value at zero filled in."""
    return np.sinc(np.asarray(x) / np.pi)


def choose_product_depth(a: float, max_t: float, small_argument: float = 1e-9) -> int:
    """Choose a safe finite depth for the sinc product on |t| <= max_t.

    Once |t| a^{-J} is tiny, the omitted logarithmic tail is quadratic and the
    truncation error is far below plotting accuracy.  A modest guard is added.
    """
    if max_t <= small_argument:
        return 8
    return max(12, int(math.ceil(math.log(max_t / small_argument, a))) + 6)


def phi_a(t: np.ndarray | float, a: float, depth: int | None = None) -> np.ndarray:
    """Evaluate a truncated infinite sinc product vectorially."""
    arr = np.asarray(t, dtype=float)
    if depth is None:
        depth = choose_product_depth(a, float(np.max(np.abs(arr))) if arr.size else 1.0)
    out = np.ones_like(arr)
    scale = 1.0 / a
    for _ in range(depth):
        out *= sinc(arr * scale)
        scale /= a
    return out


def q_pochhammer(q: mp.mpf, n: int) -> mp.mpf:
    out = mp.mpf(1)
    for j in range(1, n + 1):
        out *= 1 - q**j
    return out


def q_binomial(n: int, k: int, q: mp.mpf) -> mp.mpf:
    if k < 0 or k > n:
        return mp.mpf(0)
    return q_pochhammer(q, n) / (q_pochhammer(q, k) * q_pochhammer(q, n - k))


def spectral_moment(a: float | mp.mpf, n: int) -> mp.mpf:
    aa = mp.mpf(a)
    return aa ** (n * (n + 2)) / mp.mpf(2) ** n


def sw_coefficients(a: float | mp.mpf, n: int) -> list[mp.mpf]:
    """Ascending coefficients of the monic scaled Stieltjes-Wigert polynomial."""
    aa = mp.mpf(a)
    q = aa ** -2
    c = aa / 2
    return [
        (-1) ** (n - k) * c ** (n - k) * q ** (k * k - n * n) * q_binomial(n, k, q)
        for k in range(n + 1)
    ]


def sw_norm(a: float | mp.mpf, n: int) -> mp.mpf:
    aa = mp.mpf(a)
    q = aa ** -2
    c = aa / 2
    return c ** (2 * n) * q ** (-n * (2 * n + 1)) * q_pochhammer(q, n)


def poly_eval_ascending(coeffs: Sequence[float], z: np.ndarray) -> np.ndarray:
    out = np.zeros_like(z, dtype=float)
    for coeff in reversed(coeffs):
        out = out * z + float(coeff)
    return out


def save_figure(fig: plt.Figure, output: Path, stem: str) -> None:
    fig.tight_layout()
    fig.savefig(output / "figures" / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(output / "figures" / f"{stem}.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict[str, object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def generate_gap_geometry(output: Path, a: float = 2.6, max_generation: int = 7) -> None:
    b1 = (a - 2) / (a * (a - 1))
    gaps = [(-b1, b1)]
    rows: list[dict[str, object]] = []

    fig, ax = plt.subplots(figsize=(10, 5.2))
    for n in range(max_generation + 1):
        for left, right in gaps:
            ax.plot([left, right], [n, n], linewidth=3)
            rows.append(
                {
                    "generation": n,
                    "degree": n,
                    "left": f"{left:.17g}",
                    "right": f"{right:.17g}",
                    "length": f"{right-left:.17g}",
                }
            )
        next_gaps: list[tuple[float, float]] = []
        for left, right in gaps:
            next_gaps.append(((left - 1) / a, (right - 1) / a))
            next_gaps.append(((left + 1) / a, (right + 1) / a))
        gaps = sorted(next_gaps)

    ax.set_xlabel("x")
    ax.set_ylabel("gap generation = exact polynomial degree")
    ax.set_title(f"Polynomial-gap hierarchy for a={a}")
    ax.invert_yaxis()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "gap_hierarchy_a_2_6")
    write_csv(
        output / "data" / "gap_geometry_a_2_6.csv",
        ["generation", "degree", "left", "right", "length"],
        rows,
    )

    # Exact norm table, useful as a compact audit of the derivative scaling.
    norm_rows = []
    for n in range(11):
        c_an = (a * a / 2) ** n * a ** (n * (n - 1) / 2)
        r_an = (2 / a) ** n
        norm_rows.append(
            {
                "n": n,
                "copy_scale_c_an": f"{c_an:.17g}",
                "support_fraction_r_an": f"{r_an:.17g}",
                "L1_norm": f"{a ** (n * (n + 1) / 2):.17g}",
                "Linf_norm": f"{a ** ((n + 1) * (n + 2) / 2) / 2 ** (n + 1):.17g}",
                "L2_squared_ratio": mp.nstr(spectral_moment(a, n), 30),
            }
        )
    write_csv(
        output / "data" / "derivative_norms_a_2_6.csv",
        ["n", "copy_scale_c_an", "support_fraction_r_an", "L1_norm", "Linf_norm", "L2_squared_ratio"],
        norm_rows,
    )


def tube_volume(a: float, eps: np.ndarray) -> np.ndarray:
    b = 1 / (a - 1)
    ell0 = 2 * (a - 2) / (a * (a - 1))
    out = np.empty_like(eps)
    for idx, e in enumerate(eps):
        if e <= 0:
            out[idx] = 0
            continue
        if 2 * e >= ell0:
            # Direct gap sum handles the non-asymptotic range as well.
            total = 0.0
            n = 0
            while True:
                ell = ell0 * a ** (-n)
                term = (2**n) * min(2 * e, ell)
                total += term
                if ell < 2 * e and term < 1e-15:
                    break
                n += 1
                if n > 300:
                    break
            out[idx] = min(total, 2 * b)
        else:
            N = math.floor(math.log(ell0 / (2 * e), a))
            out[idx] = 2 * e * (2 ** (N + 1) - 1) + ell0 * (2 / a) ** (N + 1) / (1 - 2 / a)
    return out


def generate_tube_oscillation(output: Path, a: float = 3.0) -> None:
    ell0 = 2 * (a - 2) / (a * (a - 1))
    D = math.log(2) / math.log(a)
    x = np.linspace(0.05, 11.0, 2200)
    eps = (ell0 / 2) * a ** (-x)
    V = tube_volume(a, eps)
    normalized = eps ** (D - 1) * V

    fig, ax = plt.subplots(figsize=(10, 4.8))
    ax.plot(x, normalized)
    ax.set_xlabel("x = log_a(ell0/(2 epsilon))")
    ax.set_ylabel("epsilon^(D_a-1) V_a(epsilon)")
    ax.set_title(f"Log-periodic tube oscillation for a={a:g}")
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "tube_oscillation_a_3")

    write_csv(
        output / "data" / "tube_profile_a_3.csv",
        ["x", "epsilon", "tube_volume", "normalized_volume"],
        (
            {
                "x": f"{xx:.17g}",
                "epsilon": f"{ee:.17g}",
                "tube_volume": f"{vv:.17g}",
                "normalized_volume": f"{nn:.17g}",
            }
            for xx, ee, vv, nn in zip(x[::20], eps[::20], V[::20], normalized[::20])
        ),
    )


def generate_degree_limit(output: Path) -> None:
    x = np.linspace(0, 6, 1600)
    fig, ax = plt.subplots(figsize=(9.5, 4.8))
    for a in (2.5, 2.2, 2.08, 2.03):
        p = (a - 2) / a
        cdf = 1 - (1 - p) ** (np.floor(x / p).astype(int) + 1)
        ax.plot(x, cdf, label=f"a={a:g}")
    ax.plot(x, 1 - np.exp(-x), linestyle="--", linewidth=2, label="Exp(1) limit")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("P(p_a N_a <= x)")
    ax.set_title("Critical exponential limit of the local polynomial degree")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "degree_critical_limit")


def distance_survival_exact(a: float, r: np.ndarray) -> np.ndarray:
    b = 1 / (a - 1)
    ell0 = 2 * (a - 2) / (a * (a - 1))
    out = np.zeros_like(r)
    for idx, rr in enumerate(r):
        total = 0.0
        n = 0
        while True:
            ell = ell0 * a ** (-n)
            if ell <= 2 * rr:
                break
            total += 2**n * (ell - 2 * rr)
            n += 1
            if n > 400:
                break
        out[idx] = total / (2 * b)
    return out


def generate_distance_law(output: Path, a: float = 3.0) -> None:
    rng = np.random.default_rng(SEED)
    p = (a - 2) / a
    ell0 = 2 * (a - 2) / (a * (a - 1))
    size = 250_000
    # NumPy's geometric law starts at 1; subtract 1 for N in {0,1,...}.
    N = rng.geometric(p, size=size) - 1
    V = rng.random(size)
    delta = 0.5 * ell0 * a ** (-N) * V

    r = np.linspace(0, ell0 / 2, 500)
    exact = distance_survival_exact(a, r)
    delta_sorted = np.sort(delta)
    empirical = 1 - np.searchsorted(delta_sorted, r, side="right") / size

    fig, ax = plt.subplots(figsize=(9.5, 4.8))
    ax.plot(r, exact, label="exact")
    ax.plot(r, empirical, linestyle="--", label="simulation")
    ax.set_xlabel(r"$r$")
    ax.set_ylabel("P(Delta_a > r)")
    ax.set_title(f"Distance to the nonanalytic set for a={a:g}")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "distance_to_singular_set_a_3")

    write_csv(
        output / "data" / "distance_validation_a_3.csv",
        ["r", "exact_survival", "empirical_survival", "absolute_error"],
        (
            {
                "r": f"{rr:.17g}",
                "exact_survival": f"{ee:.17g}",
                "empirical_survival": f"{ss:.17g}",
                "absolute_error": f"{abs(ee-ss):.17g}",
            }
            for rr, ee, ss in zip(r[::5], exact[::5], empirical[::5])
        ),
    )


def centered_periodic_from_modes(a: float, x: np.ndarray, modes: int = 24) -> np.ndarray:
    """Evaluate P_a(x)-mean(P_a) using its exact Gamma-zeta Fourier series."""
    mp.mp.dps = 50
    L = mp.log(a)
    values = np.zeros_like(x, dtype=np.complex128)
    for k in range(1, modes + 1):
        chi = 2 * mp.pi * 1j * k / L
        coeff = -mp.gamma(-chi) * mp.zeta(1 - chi) / L
        cc = complex(coeff)
        values += cc * np.exp(2j * np.pi * k * x) + np.conjugate(cc) * np.exp(-2j * np.pi * k * x)
    return values.real


def kappa_mp(u: mp.mpf) -> mp.mpf:
    return mp.log(-mp.expm1(-u) / u)


def periodic_correction_direct(a: float, x: float) -> mp.mpf:
    """Directly evaluate P_a(x), including its mean, from the defining sums."""
    aa = mp.mpf(a)
    xx = mp.mpf(x)
    L = mp.log(aa)
    u = aa**xx

    lam = mp.mpf(0)
    uj = u / aa
    for _ in range(5000):
        term = kappa_mp(uj)
        lam += term
        if abs(term) < mp.mpf("1e-45"):
            break
        uj /= aa
    else:
        raise RuntimeError("Lambda sum failed to converge")

    R = mp.mpf(0)
    un = u
    for _ in range(5000):
        term = mp.log1p(-mp.e ** (-un))
        R += term
        if abs(term) < mp.mpf("1e-45"):
            break
        un *= aa
    else:
        raise RuntimeError("R sum failed to converge")

    return lam + L * xx * xx / 2 - L * xx / 2 + R


def generate_periodic_correction(output: Path) -> None:
    x = np.linspace(0, 1, 800, endpoint=False)
    fig, ax = plt.subplots(figsize=(10, 4.9))
    for a in (1.5, 2.0, 2.6, 3.0, 5.0):
        y = centered_periodic_from_modes(a, x)
        ax.plot(x, y, label=f"a={a:g}")
    ax.set_xlabel("x = log_a(u) mod 1")
    ax.set_ylabel("P_a(x) - mean(P_a)")
    ax.set_title("General-base logarithmic periodic correction")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "periodic_correction_bases")

    mp.mp.dps = 60
    residual_rows = []
    for a in (1.2, 1.5, 2.0, 2.6, 3.0, 5.0):
        residuals = []
        for x0 in np.linspace(-0.35, 0.65, 17):
            p0 = periodic_correction_direct(a, float(x0))
            p1 = periodic_correction_direct(a, float(x0 + 1))
            residuals.append(abs(p1 - p0))
        residual_rows.append(
            {
                "a": a,
                "max_abs_P_x_plus_1_minus_P_x": mp.nstr(max(residuals), 25),
            }
        )
    write_csv(
        output / "data" / "periodicity_residuals.csv",
        ["a", "max_abs_P_x_plus_1_minus_P_x"],
        residual_rows,
    )

    # Fourier-mode audit: numerical quadrature of the direct periodic function.
    mode_rows = []
    a = 2.6
    grid = np.linspace(0, 1, 1024, endpoint=False)
    direct = np.array([float(periodic_correction_direct(a, float(xx))) for xx in grid])
    direct -= direct.mean()
    fft = np.fft.fft(direct) / len(grid)
    L = mp.log(a)
    for k in range(1, 9):
        chi = 2 * mp.pi * 1j * k / L
        exact = complex(-mp.gamma(-chi) * mp.zeta(1 - chi) / L)
        numeric = fft[k]
        mode_rows.append(
            {
                "k": k,
                "numeric_real": f"{numeric.real:.17g}",
                "numeric_imag": f"{numeric.imag:.17g}",
                "exact_real": f"{exact.real:.17g}",
                "exact_imag": f"{exact.imag:.17g}",
                "absolute_error": f"{abs(numeric-exact):.17g}",
            }
        )
    write_csv(
        output / "data" / "gamma_zeta_modes_a_2_6.csv",
        ["k", "numeric_real", "numeric_imag", "exact_real", "exact_imag", "absolute_error"],
        mode_rows,
    )


def exact_moments_from_cumulants(a: float, max_order: int) -> list[mp.mpf]:
    mp.mp.dps = 80
    kappa = [mp.mpf(0)] * (max_order + 1)
    for n in range(2, max_order + 1, 2):
        m = n // 2
        kappa[n] = 2 ** (2 * m) * mp.bernoulli(2 * m) / (2 * m * (mp.mpf(a) ** (2 * m) - 1))
    mu = [mp.mpf(0)] * (max_order + 1)
    mu[0] = 1
    for n in range(1, max_order + 1):
        mu[n] = sum(mp.binomial(n - 1, j - 1) * kappa[j] * mu[n - j] for j in range(1, n + 1))
    return mu


def generate_moment_validation(output: Path, a: float = 2.6) -> None:
    rng = np.random.default_rng(SEED)
    size = 250_000
    # Tail bound sum_{j>J} a^{-j} <= a^{-J}/(a-1).
    J = math.ceil(math.log(1e12 / (a - 1), a)) + 2
    samples = np.zeros(size)
    scale = 1 / a
    for _ in range(J):
        samples += scale * rng.uniform(-1, 1, size=size)
        scale /= a

    exact = exact_moments_from_cumulants(a, 10)
    rows = []
    for n in range(0, 11):
        empirical = float(np.mean(samples**n))
        ex = float(exact[n])
        rows.append(
            {
                "order": n,
                "exact": f"{ex:.17g}",
                "monte_carlo": f"{empirical:.17g}",
                "absolute_error": f"{abs(empirical-ex):.17g}",
                "relative_error": f"{abs(empirical-ex)/max(1e-300,abs(ex)):.17g}" if ex != 0 else "",
                "terms_used": J,
                "deterministic_tail_bound": f"{a**(-J)/(a-1):.17g}",
            }
        )
    write_csv(
        output / "data" / "moment_validation_a_2_6.csv",
        ["order", "exact", "monte_carlo", "absolute_error", "relative_error", "terms_used", "deterministic_tail_bound"],
        rows,
    )


def generate_gaussian_limit(output: Path) -> None:
    a = np.linspace(1.001, 1.7, 1200)
    exact = -(6 / 5) * (a * a - 1) / (a * a + 1)
    first = -(6 / 5) * (a - 1)
    fig, ax = plt.subplots(figsize=(9.5, 4.8))
    ax.plot(a - 1, exact, label="exact standardized fourth cumulant")
    ax.plot(a - 1, first, linestyle="--", label="first term -(6/5)(a-1)")
    ax.set_xlabel("a - 1")
    ax.set_ylabel("standardized fourth cumulant")
    ax.set_title("Gaussian-limit cumulant scaling")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "gaussian_cumulant_limit")


def spectral_log_grid(a: float, x_min: float = -40, x_max: float = 36, points: int = 50000):
    x = np.linspace(x_min, x_max, points)
    z = np.exp(x)
    t = np.exp(x / 2)
    phi = phi_a(t, a)
    raw = phi * phi * np.exp(x / 2)  # e^x * |Phi(sqrt(e^x))|^2 / sqrt(e^x)
    integral = np.trapezoid(raw, x)
    return x, z, raw / integral, integral


def generate_spectral_twin(output: Path, a: float = 2.6) -> None:
    x, z, g_sp, I_approx = spectral_log_grid(a)
    mu = 2 * math.log(a) - math.log(2)
    sigma2 = 2 * math.log(a)
    g_ln = np.exp(-((x - mu) ** 2) / (2 * sigma2)) / math.sqrt(2 * math.pi * sigma2)

    fig, ax = plt.subplots(figsize=(10, 4.9))
    ax.plot(x, g_sp, label="sinc-product spectral representative")
    ax.plot(x, g_ln, linestyle="--", label="lognormal moment twin")
    ax.set_xlim(-10, 16)
    ax.set_xlabel("x = log z")
    ax.set_ylabel("density of log Z")
    ax.set_title(f"Distinct representatives of the same moments, a={a}")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "spectral_lognormal_general_base")

    rows = []
    for n in range(0, 7):
        # Log-grid quadrature.  The chosen interval contains the moving saddle for these orders.
        numeric = np.trapezoid(g_sp * np.exp(n * x), x)
        exact = float(spectral_moment(a, n))
        rows.append(
            {
                "n": n,
                "quadrature": f"{numeric:.17g}",
                "exact": f"{exact:.17g}",
                "absolute_error": f"{abs(numeric-exact):.17g}",
                "relative_error": f"{abs(numeric-exact)/exact:.17g}" if exact else "0",
                "unnormalized_Ia_quadrature": f"{I_approx:.17g}",
            }
        )
    write_csv(
        output / "data" / "spectral_moment_validation_a_2_6.csv",
        ["n", "quadrature", "exact", "absolute_error", "relative_error", "unnormalized_Ia_quadrature"],
        rows,
    )

    # The normalization cancels from the q-Pearson equation.
    z_test = np.logspace(-8, 8, 800)
    lhs = phi_a(a * np.sqrt(z_test), a) ** 2 / (a * np.sqrt(z_test))
    rhs = (1 / a) * sinc(np.sqrt(z_test)) ** 2 * (phi_a(np.sqrt(z_test), a) ** 2 / np.sqrt(z_test))
    residual = np.abs(lhs - rhs)
    scale = np.maximum(np.abs(lhs), np.abs(rhs))
    write_csv(
        output / "data" / "spectral_q_pearson_a_2_6.csv",
        ["z", "lhs", "rhs", "absolute_error", "relative_error"],
        (
            {
                "z": f"{zz:.17g}",
                "lhs": f"{ll:.17g}",
                "rhs": f"{rr:.17g}",
                "absolute_error": f"{ee:.17g}",
                "relative_error": f"{ee/max(ss,1e-300):.17g}",
            }
            for zz, ll, rr, ee, ss in zip(z_test[::8], lhs[::8], rhs[::8], residual[::8], scale[::8])
        ),
    )


def generate_orthogonal_ladder(output: Path, a: float = 2.6, max_n: int = 5) -> None:
    mp.mp.dps = 100
    coeffs = [sw_coefficients(a, n) for n in range(max_n + 1)]
    norms = [sw_norm(a, n) for n in range(max_n + 1)]

    gram = [[mp.mpf(0) for _ in range(max_n + 1)] for _ in range(max_n + 1)]
    for n in range(max_n + 1):
        for m in range(max_n + 1):
            value = mp.mpf(0)
            for k, ck in enumerate(coeffs[n]):
                for ell, cl in enumerate(coeffs[m]):
                    value += ck * cl * spectral_moment(a, k + ell)
            gram[n][m] = value / mp.sqrt(norms[n] * norms[m])

    rows = []
    for n in range(max_n + 1):
        for m in range(max_n + 1):
            expected = mp.mpf(1) if n == m else mp.mpf(0)
            rows.append(
                {
                    "n": n,
                    "m": m,
                    "normalized_gram": mp.nstr(gram[n][m], 40),
                    "expected": int(n == m),
                    "absolute_error": mp.nstr(abs(gram[n][m] - expected), 15),
                }
            )
    write_csv(
        output / "data" / "orthogonal_ladder_validation_a_2_6.csv",
        ["n", "m", "normalized_gram", "expected", "absolute_error"],
        rows,
    )

    # Plot the first four orthonormal modes in the log spectral variable.
    x, z, g_sp, _ = spectral_log_grid(a, x_min=-30, x_max=20, points=40000)
    mask = (x >= -8) & (x <= 13)
    fig, ax = plt.subplots(figsize=(10, 5.1))
    for n in range(4):
        cf = [float(v) for v in coeffs[n]]
        pz = poly_eval_ascending(cf, z)
        mode = pz * np.sqrt(np.maximum(g_sp, 0) / float(norms[n]))
        ax.plot(x[mask], mode[mask], label=f"n={n}")
    ax.set_xlabel("x = log z")
    ax.set_ylabel("normalized mode amplitude")
    ax.set_title(f"Scaled Stieltjes-Wigert spectral modes for a={a}")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "orthogonal_derivative_ladder_a_2_6")

    # Determinant audit for even and odd derivative jets (with ||h||_2 set to 1).
    q = mp.mpf(a) ** -2
    c = mp.mpf(a) / 2
    det_rows = []
    for N in range(0, 7):
        even_matrix = mp.matrix([[(-1) ** (i + j) * spectral_moment(a, i + j) for j in range(N + 1)] for i in range(N + 1)])
        odd_matrix = mp.matrix([[(-1) ** (i + j) * spectral_moment(a, i + j + 1) for j in range(N + 1)] for i in range(N + 1)])
        even_num = mp.det(even_matrix)
        odd_num = mp.det(odd_matrix)
        prod = mp.fprod(q_pochhammer(q, k) for k in range(1, N + 1)) if N > 0 else mp.mpf(1)
        even_exact = c ** (N * (N + 1)) * q ** (-N * (N + 1) * (4 * N + 5) / 6) * prod
        odd_exact = c ** ((N + 1) ** 2) * q ** (-(N + 1) * (N + 2) * (4 * N + 3) / 6) * prod
        det_rows.append(
            {
                "N": N,
                "even_numeric": mp.nstr(even_num, 35),
                "even_exact": mp.nstr(even_exact, 35),
                "even_relative_error": mp.nstr(abs(even_num / even_exact - 1), 12),
                "odd_numeric": mp.nstr(odd_num, 35),
                "odd_exact": mp.nstr(odd_exact, 35),
                "odd_relative_error": mp.nstr(abs(odd_num / odd_exact - 1), 12),
            }
        )
    write_csv(
        output / "data" / "derivative_gram_determinants_a_2_6.csv",
        ["N", "even_numeric", "even_exact", "even_relative_error", "odd_numeric", "odd_exact", "odd_relative_error"],
        det_rows,
    )

    # Save coefficients and recurrence coefficients for independent reuse.
    coeff_rows = []
    for n, cf in enumerate(coeffs):
        for k, value in enumerate(cf):
            coeff_rows.append({"n": n, "k": k, "coefficient_of_z_k": mp.nstr(value, 40)})
    write_csv(
        output / "data" / "stieltjes_wigert_coefficients_a_2_6.csv",
        ["n", "k", "coefficient_of_z_k"],
        coeff_rows,
    )


def generate_autocorrelation_jet(output: Path) -> None:
    n = np.arange(0, 21)
    fig, ax = plt.subplots(figsize=(9.5, 4.8))
    rows = []
    for a in (2.0, 2.6, 3.0):
        log10_values = (n * (n + 2) * math.log(a) - n * math.log(2)) / math.log(10)
        ax.plot(n, log10_values, marker="o", markersize=3, label=f"a={a:g}")
        for nn, vv in zip(n, log10_values):
            rows.append(
                {
                    "a": a,
                    "n": int(nn),
                    "log10_normalized_abs_derivative": f"{vv:.17g}",
                    "exact_ratio": mp.nstr(spectral_moment(a, int(nn)), 35),
                }
            )
    ax.set_xlabel("n")
    ax.set_ylabel("log10 normalized absolute autocorrelation derivative")
    ax.set_title("Quadratic growth of the autocorrelation jet")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, output, "autocorrelation_jet_growth")
    write_csv(
        output / "data" / "autocorrelation_jet.csv",
        ["a", "n", "log10_normalized_abs_derivative", "exact_ratio"],
        rows,
    )


def write_requirements_and_readme(output: Path) -> None:
    (output / "requirements.txt").write_text(
        "numpy>=2.0\nmatplotlib>=3.8\nmpmath>=1.3\n",
        encoding="utf-8",
    )
    readme = """# Atomic Functions Beyond the Critical Dyadic Case

This archive contains the English reconstruction and expansion of the attached Rvachev chapter.

## Build

```bash
python experiments.py --output .
latexmk -pdf -interaction=nonstopmode -halt-on-error Atomic_Functions_Beyond_Dyadic_Expanded.tex
```

The script uses the fixed seed `20260828`. All figures are written in PDF and PNG formats, and the numerical audits are written to `data/`.

## Status markers in the report

- `[S]`: translated or reconstructed source material.
- `[R]`: repository or established literature connection.
- `[N]`: proved deduction in the report, without a priority claim.
- `[F]`: post-audit frontier formula not found in the inspected repository snapshot.
- `[C]`: conjecture or research program.
"""
    (output / "README.md").write_text(readme, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("."), help="report directory")
    args = parser.parse_args()
    output = args.output.resolve()
    (output / "figures").mkdir(parents=True, exist_ok=True)
    (output / "data").mkdir(parents=True, exist_ok=True)

    generate_gap_geometry(output)
    generate_tube_oscillation(output)
    generate_degree_limit(output)
    generate_distance_law(output)
    generate_periodic_correction(output)
    generate_moment_validation(output)
    generate_gaussian_limit(output)
    generate_spectral_twin(output)
    generate_orthogonal_ladder(output)
    generate_autocorrelation_jet(output)
    write_requirements_and_readme(output)
    print(f"Generated figures and audit tables in {output}")


if __name__ == "__main__":
    main()
