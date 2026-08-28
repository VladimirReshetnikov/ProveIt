#!/usr/bin/env python3
"""Numerical experiments for the Fabius--Rvachev representation report.

The program checks four identities developed or synthesized in the report:

1. The dyadic-gamma factorization
       Phi(z) = 1 / (Gamma_dy(z) Gamma_dy(-z)).
2. Jensen's circular-mean formula for the zero divisor of Phi.
3. Equality in law between the dyadic logistic series and a Gaussian
   variance mixture driven by the spectral gamma convolution.
4. The sine-series representation of the bounded Fabius function.

All random experiments use a fixed seed.  Infinite products and random series
are truncated only after explicit tail controls are applied.  The output is a
plain-text audit trail plus four figures.  The script is intentionally
self-contained and does not require network access.

Fourier convention used throughout:
    f_hat(xi) = integral_R f(x) exp(-2*pi*i*x*xi) dx.

Run from the package directory with
    python numerical_experiments.py
or choose a different output directory with
    python numerical_experiments.py --output-dir path/to/output
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.special import loggamma, zeta
from scipy.stats import ks_2samp


PI = math.pi


def v2(n: int) -> int:
    """Return the 2-adic valuation of the positive integer n."""
    if n <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (n & -n).bit_length() - 1


def multiplicity(n: int) -> int:
    """Zero multiplicity a_n = 1 + v_2(n) in the canonical product."""
    return 1 + v2(n)


def _sinc_pi_complex(z: np.ndarray) -> np.ndarray:
    """Vectorized sin(pi*z)/(pi*z), with the removable value at zero."""
    w = PI * z
    out = np.ones_like(w, dtype=np.complex128)
    mask = np.abs(w) > 1.0e-14
    out[mask] = np.sin(w[mask]) / w[mask]
    return out


def phi_sinc(z: np.ndarray | complex | float, layers: int = 60) -> np.ndarray:
    """Evaluate Phi by the dyadic sinc product.

    For bounded z, omitted factors differ from one by O(|z|^2 4^{-layers}),
    so 60 layers are far beyond double-precision requirements in these tests.
    """
    arr = np.asarray(z, dtype=np.complex128)
    result = np.ones_like(arr, dtype=np.complex128)
    for h in range(layers):
        result *= _sinc_pi_complex(arr / (2.0**h))
    return result


def phi_real_scalar(x: float, layers: int = 60) -> float:
    """Fast scalar real evaluation used inside numerical quadrature."""
    result = 1.0
    for h in range(layers):
        w = PI * x / (2.0**h)
        result *= 1.0 if abs(w) < 1.0e-15 else math.sin(w) / w
    return result


def gamma_dy(z: complex, layers: int = 60) -> complex:
    """Evaluate Gamma_dy(z) = product_{h>=0} Gamma(1+z/2^h).

    Summation of logarithms avoids overflow and preserves relative accuracy.
    The test points stay away from the pole set {-1,-2,...}.
    """
    total = 0.0j
    for h in range(layers):
        total += loggamma(1.0 + z / (2.0**h))
    return complex(np.exp(total))


def jensen_exact(radius: float) -> float:
    """Exact Jensen mean 2*sum_{n<=r} a_n log(r/n)."""
    if radius <= 0:
        raise ValueError("radius must be positive")
    nmax = int(math.floor(radius))
    return 2.0 * sum(
        multiplicity(n) * math.log(radius / n) for n in range(1, nmax + 1)
    )


def jensen_numerical(radius: float, angles: int = 16384) -> float:
    """Trapezoidal angular average of log|Phi(r exp(i theta))|."""
    theta = 2.0 * PI * np.arange(angles) / angles
    values = phi_sinc(radius * np.exp(1.0j * theta))
    return float(np.mean(np.log(np.abs(values))))


def logistic_dual_cf(t: np.ndarray, layers: int = 60) -> np.ndarray:
    """Exact characteristic function of the dyadic logistic dual.

    phi_Z(t) = product_{j>=1} (t/2^j)/sinh(t/2^j).
    The calculation is performed in the logarithmic domain.
    """
    t = np.asarray(t, dtype=float)
    log_cf = np.zeros_like(t)
    for j in range(1, layers + 1):
        x = t / (2.0**j)
        ratio = np.ones_like(x)
        mask = np.abs(x) > 1.0e-12
        ratio[mask] = x[mask] / np.sinh(x[mask])
        # ratio is positive for real x.
        log_cf += np.log(ratio)
    return np.exp(log_cf)


def spectral_tail_sum(power: int, cutoff: int, layers: int = 80) -> float:
    """Compute sum_{n>cutoff} a_n/n^power from its dyadic-layer identity.

    Since a_n = sum_{h>=0} 1_{2^h | n},
        sum_{n>N} a_n/n^p
      = sum_{h>=0} 2^{-hp} [zeta(p)-H_{floor(N/2^h)}^{(p)}].
    The final geometric tail (where the floor is zero) is also included.
    """
    if power <= 1:
        raise ValueError("power must exceed one")
    zeta_p = float(zeta(power, 1.0))
    total = 0.0
    h = 0
    while h < layers:
        m = cutoff // (2**h)
        if m == 0:
            # All later harmonic cutoffs are also zero; sum the geometric tail.
            total += zeta_p * (2.0 ** (-h * power)) / (1.0 - 2.0 ** (-power))
            break
        harmonic = sum(1.0 / (k**power) for k in range(1, m + 1))
        total += (2.0 ** (-h * power)) * (zeta_p - harmonic)
        h += 1
    return total


def simulate_dual_laws(
    samples: int,
    logistic_layers: int,
    gamma_cutoff: int,
    seed: int,
) -> tuple[np.ndarray, np.ndarray, dict[str, float]]:
    """Simulate the two laws in the Gaussian-mixture bridge.

    Logistic side:
        Z_log = sum_j Lambda_j/(pi*2^j).

    Mixture side:
        V = sum_n Gamma(a_n, rate=n^2),
        Z_mix = sqrt(V)/(sqrt(2)*pi) * N(0,1).

    The positive gamma tail is extremely concentrated.  We add its exact mean;
    its omitted standard deviation is reported so the approximation is auditable.
    """
    rng = np.random.default_rng(seed)

    z_log = np.zeros(samples)
    for j in range(1, logistic_layers + 1):
        z_log += rng.logistic(size=samples) / (PI * (2.0**j))

    v = np.zeros(samples)
    # Chunking keeps peak memory low even for large sample counts.
    chunk = 5000
    ns = np.arange(1, gamma_cutoff + 1)
    shapes = np.array([multiplicity(int(n)) for n in ns], dtype=float)
    scales = 1.0 / (ns.astype(float) ** 2)
    for start in range(0, samples, chunk):
        stop = min(start + chunk, samples)
        draw = rng.gamma(
            shape=shapes[None, :],
            scale=scales[None, :],
            size=(stop - start, gamma_cutoff),
        )
        v[start:stop] = np.sum(draw, axis=1)

    tail_mean = spectral_tail_sum(2, gamma_cutoff)
    tail_variance = spectral_tail_sum(4, gamma_cutoff)
    v += tail_mean
    z_mix = np.sqrt(v) * rng.normal(size=samples) / (math.sqrt(2.0) * PI)

    logistic_tail_sd = 2.0 ** (-logistic_layers) / 3.0
    diagnostics = {
        "gamma_tail_mean": tail_mean,
        "gamma_tail_sd": math.sqrt(tail_variance),
        "logistic_tail_sd": logistic_tail_sd,
    }
    return z_log, z_mix, diagnostics


def fabius_sine_series(x: float, terms: int) -> float:
    """Evaluate F(x) from the odd-harmonic sine series."""
    n = np.arange(1, 2 * terms, 2, dtype=float)
    coefficients = phi_sinc(n / 2.0).real
    return float(x - np.sum(coefficients * np.sin(2.0 * PI * n * x) / (PI * n)))


def fabius_fourier_integral(x: float, cutoff: int = 30) -> float:
    """Independent reference from the Fourier inversion integral.

    F(x) = 1/2 + (1/pi) int_0^infty Phi(t) sin(2*pi*t*(2x-1))/t dt.
    The integral is split at integer zeros.  Past 30, the smooth compact-support
    transform is already below the requested double-precision tolerance.
    """
    a = 2.0 * x - 1.0

    def integrand(t: float) -> float:
        if t == 0.0:
            return 2.0 * PI * a
        return phi_real_scalar(t) * math.sin(2.0 * PI * t * a) / t

    total = 0.0
    for n in range(cutoff):
        value, _ = quad(
            integrand,
            float(n),
            float(n + 1),
            epsabs=2.0e-13,
            epsrel=2.0e-13,
            limit=200,
        )
        total += value
    return 0.5 + total / PI


def save_gamma_figure(output_dir: Path, log_lines: list[str]) -> None:
    points = [0.3 + 0.0j, 0.4 + 0.2j, -0.6 + 0.1j]
    layers = np.arange(4, 61, 2)
    errors = []
    for h in layers:
        point_errors = []
        for z in points:
            lhs = complex(phi_sinc(z, layers=int(h)))
            rhs = 1.0 / (gamma_dy(z, int(h)) * gamma_dy(-z, int(h)))
            point_errors.append(abs(lhs - rhs) / max(1.0, abs(lhs)))
        errors.append(max(point_errors))

    plt.figure(figsize=(7.2, 4.5))
    plt.semilogy(layers, errors, marker="o")
    plt.xlabel("dyadic product layers")
    plt.ylabel("maximum relative discrepancy")
    plt.title("Dyadic-gamma factorization check")
    plt.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    path = output_dir / "gamma_factorization_convergence.png"
    plt.savefig(path, dpi=180)
    plt.close()

    log_lines.append("DYADIC-GAMMA FACTORIZATION")
    for z in points:
        lhs = complex(phi_sinc(z, layers=60))
        rhs = 1.0 / (gamma_dy(z, 60) * gamma_dy(-z, 60))
        fe_lhs = gamma_dy(z, 60)
        fe_rhs = complex(np.exp(loggamma(1.0 + z))) * gamma_dy(z / 2.0, 60)
        log_lines.append(
            f"  z={z!s:>12}: |Phi - factorization|={abs(lhs-rhs):.3e}; "
            f"functional-equation error={abs(fe_lhs-fe_rhs):.3e}"
        )
    log_lines.append("")


def save_jensen_figure(output_dir: Path, log_lines: list[str]) -> None:
    radii = np.linspace(0.25, 12.75, 76)
    # Shift points that accidentally land too near an integer zero on the circle.
    radii = np.array([r + 0.031 if abs(r - round(r)) < 0.02 else r for r in radii])
    exact = np.array([jensen_exact(float(r)) for r in radii])
    numerical = np.array([jensen_numerical(float(r), angles=8192) for r in radii])
    discrepancy = np.max(np.abs(exact - numerical))

    plt.figure(figsize=(7.2, 4.5))
    plt.plot(radii, exact, label="exact zero-divisor formula")
    plt.plot(radii, numerical, linestyle="--", label="angular quadrature")
    plt.xlabel("radius r")
    plt.ylabel("circular mean of log|Phi|")
    plt.title("Jensen mean and the binary zero divisor")
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    path = output_dir / "jensen_mean_comparison.png"
    plt.savefig(path, dpi=180)
    plt.close()

    log_lines.append("JENSEN CIRCULAR MEAN")
    log_lines.append(f"  maximum absolute discrepancy on 76 radii: {discrepancy:.3e}")
    for r in [0.6, 1.4, 3.7, 10.3]:
        num = jensen_numerical(r, angles=32768)
        ex = jensen_exact(r)
        log_lines.append(
            f"  r={r:4.1f}: numerical={num:.15e}, exact={ex:.15e}, error={num-ex:.3e}"
        )
    log_lines.append("")


def save_mixture_figure(output_dir: Path, log_lines: list[str]) -> None:
    samples = 100_000
    z_log, z_mix, diagnostics = simulate_dual_laws(
        samples=samples,
        logistic_layers=16,
        gamma_cutoff=250,
        seed=20260827,
    )
    t_grid = np.linspace(0.0, 14.0, 120)
    exact = logistic_dual_cf(t_grid)
    empirical_log = np.array([np.mean(np.cos(t * z_log)) for t in t_grid])
    empirical_mix = np.array([np.mean(np.cos(t * z_mix)) for t in t_grid])

    plt.figure(figsize=(7.2, 4.5))
    plt.plot(t_grid, exact, label="exact characteristic function")
    plt.plot(t_grid, empirical_log, linestyle="--", label="dyadic logistic simulation")
    plt.plot(t_grid, empirical_mix, linestyle=":", label="Gaussian-mixture simulation")
    plt.xlabel("frequency t")
    plt.ylabel("characteristic function")
    plt.title("Logistic series = Gaussian variance mixture")
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    path = output_dir / "gaussian_mixture_characteristic_function.png"
    plt.savefig(path, dpi=180)
    plt.close()

    ks = ks_2samp(z_log, z_mix)
    max_cf_log = float(np.max(np.abs(empirical_log - exact)))
    max_cf_mix = float(np.max(np.abs(empirical_mix - exact)))
    log_lines.append("GAUSSIAN VARIANCE-MIXTURE BRIDGE")
    log_lines.append(f"  samples per construction: {samples}")
    log_lines.append(
        f"  KS statistic logistic-series versus mixture: {ks.statistic:.4e} "
        f"(two-sample p-value {ks.pvalue:.4f})"
    )
    log_lines.append(f"  max empirical-CF error, logistic series: {max_cf_log:.4e}")
    log_lines.append(f"  max empirical-CF error, Gaussian mixture: {max_cf_mix:.4e}")
    log_lines.append(
        f"  sample variances: logistic={np.var(z_log):.9f}, "
        f"mixture={np.var(z_mix):.9f}, exact=1/9={1/9:.9f}"
    )
    log_lines.append(
        "  truncation diagnostics: "
        f"gamma tail mean={diagnostics['gamma_tail_mean']:.4e}, "
        f"gamma tail sd={diagnostics['gamma_tail_sd']:.4e}, "
        f"logistic tail sd={diagnostics['logistic_tail_sd']:.4e}"
    )
    log_lines.append("")


def save_fabius_figure(output_dir: Path, log_lines: list[str]) -> None:
    x_values = np.array([0.05, 0.10, 0.18, 0.25, 0.33, 0.40, 0.62, 0.75, 0.90, 0.95])
    references = np.array([fabius_fourier_integral(float(x)) for x in x_values])
    term_counts = np.array([1, 2, 4, 8, 16, 32, 64, 128])
    errors = []
    for terms in term_counts:
        approximations = np.array([fabius_sine_series(float(x), int(terms)) for x in x_values])
        errors.append(float(np.max(np.abs(approximations - references))))

    plt.figure(figsize=(7.2, 4.5))
    plt.semilogy(term_counts, errors, marker="o")
    plt.xlabel("number of odd harmonics")
    plt.ylabel("maximum absolute error")
    plt.title("Convergence of the Fabius sine series")
    plt.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    path = output_dir / "fabius_sine_series_convergence.png"
    plt.savefig(path, dpi=180)
    plt.close()

    log_lines.append("FABIUS SINE SERIES")
    for x, ref in zip(x_values, references):
        approx = fabius_sine_series(float(x), 128)
        log_lines.append(
            f"  x={x:4.2f}: Fourier integral={ref:.15e}, "
            f"128-term series={approx:.15e}, error={approx-ref:.3e}"
        )
    log_lines.append(
        "  max errors by term count: "
        + ", ".join(f"K={k}:{err:.2e}" for k, err in zip(term_counts, errors))
    )
    log_lines.append("")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "figures",
        help="directory for figures and numerical_results.txt",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_dir: Path = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    log_lines: list[str] = [
        "Fabius--Rvachev representation experiments",
        "deterministic seed: 20260827",
        "double-precision calculations unless stated otherwise",
        "",
    ]
    save_gamma_figure(output_dir, log_lines)
    save_jensen_figure(output_dir, log_lines)
    save_mixture_figure(output_dir, log_lines)
    save_fabius_figure(output_dir, log_lines)

    result_path = output_dir / "numerical_results.txt"
    result_path.write_text("\n".join(log_lines), encoding="utf-8")
    print("\n".join(log_lines))
    print(f"Wrote figures and audit trail to {output_dir}")


if __name__ == "__main__":
    main()
