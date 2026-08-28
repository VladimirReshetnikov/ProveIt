#!/usr/bin/env python3
"""
Numerical experiments for
  Integral Transforms and Fractional Calculus for the Fabius and Rvachev Functions.

The script deliberately avoids black-box samples of the Fabius function.  It uses
three independent representations:

1. Exact rational cumulants and moments (Bernoulli/Bell recurrence).
2. A finite weighted-Irwin-Hall spline for the first N binary-uniform summands.
   The unresolved tail is replaced by its mean.  Because the binary weights are
   powers of two, the inclusion-exclusion signs are exactly the Thue-Morse signs.
3. Infinite products for the Laplace/Fourier transforms.

Outputs:
  * numerical_results.txt
  * moment_table.tex
  * fractional_dilation_defect.png
  * gamma_zeta_fractional_defect.png

The calculations are verification experiments, not substitutes for the proofs in
LaTeX.  Default parameters are chosen for reproducibility on an ordinary laptop.
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Callable, Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gamma

HERE = Path(__file__).resolve().parent

# ---------------------------------------------------------------------------
# 1. Exact Bernoulli cumulants and complete-Bell moments
# ---------------------------------------------------------------------------

def exact_moments(max_order: int = 16) -> tuple[list[sp.Expr], list[sp.Expr], list[sp.Expr]]:
    """Return cumulants of Y, moments of Y, and centered moments of Z=2Y-1.

    Here
        Y = sum_{k>=1} 2^{-k} V_k,  V_k ~ Uniform[0,1],
        Z = 2Y-1,
    so Y has CDF F and Z has density up.

    For n>=2,
        kappa_n(Y) = B_n / (n (2^n-1)).
    The moment-cumulant recurrence is the complete exponential Bell recurrence.
    """
    kappa_y = [sp.Integer(0)] * (max_order + 1)
    kappa_y[1] = sp.Rational(1, 2)
    for n in range(2, max_order + 1):
        kappa_y[n] = sp.bernoulli(n) / (n * (2**n - 1))

    mu = [sp.Integer(0)] * (max_order + 1)
    mu[0] = sp.Integer(1)
    for n in range(1, max_order + 1):
        mu[n] = sp.simplify(
            sum(
                sp.binomial(n - 1, k - 1) * kappa_y[k] * mu[n - k]
                for k in range(1, n + 1)
            )
        )

    kappa_z = [sp.Integer(0)] * (max_order + 1)
    for n in range(2, max_order + 1):
        kappa_z[n] = sp.simplify((sp.Integer(2) ** n) * kappa_y[n])

    moment_z = [sp.Integer(0)] * (max_order + 1)
    moment_z[0] = sp.Integer(1)
    for n in range(1, max_order + 1):
        moment_z[n] = sp.simplify(
            sum(
                sp.binomial(n - 1, k - 1) * kappa_z[k] * moment_z[n - k]
                for k in range(1, n + 1)
            )
        )
    return kappa_y, mu, moment_z


KAPPA_Y, MU_EXACT, MZ_EXACT = exact_moments(20)


# ---------------------------------------------------------------------------
# 2. Deterministic finite-spline approximation of F
# ---------------------------------------------------------------------------

class FabiusSplineApproximation:
    """Centered finite-spline approximation to the Fabius distribution.

    Let S_N = sum_{k=1}^N 2^{-k} V_k.  The omitted tail has support [0,2^{-N}]
    and mean 2^{-N-1}.  We approximate Y by S_N plus that mean.

    For S_N the weighted Irwin-Hall inclusion-exclusion formula is

      P(S_N <= x) = 2^{N(N+1)/2}/N! * sum_m eps_m (x-m/2^N)_+^N,

    where eps_m=(-1)^{popcount(m)} is the Thue-Morse sign.  Long-double
    arithmetic is adequate through about N=12 in the stable half interval.
    Exact reflection about 1/2 is then used to avoid cancellation on the right.
    """

    def __init__(self, level: int = 11) -> None:
        if not 4 <= level <= 13:
            raise ValueError("level should normally lie between 4 and 13")
        self.level = level
        self.size = 2**level
        self.tail = float(2.0 ** (-level))
        self.shifts = np.arange(self.size, dtype=np.longdouble) / np.longdouble(self.size)
        self.signs = np.array(
            [1 if i.bit_count() % 2 == 0 else -1 for i in range(self.size)],
            dtype=np.longdouble,
        )
        self.factor = (
            np.longdouble(2) ** (level * (level + 1) // 2)
        ) / np.longdouble(math.factorial(level))

    def _cdf_partial_sum(self, x: float) -> float:
        """CDF of S_N before centering the omitted tail."""
        if x <= 0.0:
            return 0.0
        if x >= 1.0 - self.tail:
            return 1.0
        xx = np.longdouble(x)
        z = xx - self.shifts
        mask = z > 0
        value = self.factor * np.sum(
            self.signs[mask] * z[mask] ** self.level,
            dtype=np.longdouble,
        )
        return float(value)

    def __call__(self, x: float) -> float:
        """Approximate bounded F(x), preserving F(1-x)=1-F(x) exactly."""
        if x <= 0.0:
            return 0.0
        if x >= 1.0:
            return 1.0
        if x > 0.5:
            return 1.0 - self(1.0 - x)
        value = self._cdf_partial_sum(x - self.tail / 2.0)
        return min(1.0, max(0.0, value))

    def inverse(self, y: float) -> float:
        """Numerical inverse of the centered spline approximation."""
        if y <= 0.0:
            return 0.0
        if y >= 1.0:
            return 1.0
        if abs(y - 0.5) <= 5e-10:
            return 0.5
        if y > 0.5:
            return 1.0 - self.inverse(1.0 - y)
        return float(
            brentq(
                lambda x: self(x) - y,
                0.0,
                0.5,
                xtol=2e-13,
                rtol=2e-13,
                maxiter=100,
            )
        )


F_APPROX = FabiusSplineApproximation(level=11)


def rl_integral_F(alpha: float, x: float, F: Callable[[float], float] = F_APPROX) -> float:
    """Compute (I_{0+}^alpha F)(x) without an endpoint singularity.

    Substituting u=v^(1/alpha) converts the beta-kernel integral to

      x^alpha/Gamma(alpha+1) * integral_0^1 F(x(1-v^(1/alpha))) dv.
    """
    if alpha <= 0.0:
        raise ValueError("alpha must be positive")
    if x <= 0.0:
        return 0.0
    value = quad(
        lambda v: F(x * (1.0 - v ** (1.0 / alpha))),
        0.0,
        1.0,
        epsabs=2e-10,
        epsrel=2e-10,
        limit=250,
    )[0]
    return x**alpha * value / gamma(alpha + 1.0)


def mu_numeric(s: float, F: Callable[[float], float] = F_APPROX) -> float:
    """Numerical analytic moment mu(s)=E(Y^s), for s>0.

    Integration by parts gives mu(s)=s*int_0^1 x^(s-1)(1-F(x)) dx.
    """
    if s <= 0.0:
        raise ValueError("this numerical quadrature expects s>0")
    value = quad(
        lambda x: x ** (s - 1.0) * (1.0 - F(x)),
        0.0,
        1.0,
        epsabs=2e-10,
        epsrel=2e-10,
        limit=300,
    )[0]
    return s * value


def rl_integral_inverse_direct(alpha: float, y: float) -> float:
    """Directly integrate the approximate inverse G with the RL kernel."""
    value = quad(
        lambda v: F_APPROX.inverse(y * (1.0 - v ** (1.0 / alpha))),
        0.0,
        1.0,
        epsabs=3e-8,
        epsrel=3e-8,
        limit=180,
    )[0]
    return y**alpha * value / gamma(alpha + 1.0)


def rl_integral_inverse_transmuted(alpha: float, y: float) -> float:
    """Use the proved quantile-transmutation identity.

      I^alpha G(y) = 1/Gamma(alpha+1) * int_0^{G(y)} (y-F(x))^alpha dx.
    """
    gy = F_APPROX.inverse(y)
    value = quad(
        lambda x: max(y - F_APPROX(x), 0.0) ** alpha,
        0.0,
        gy,
        epsabs=3e-8,
        epsrel=3e-8,
        limit=180,
    )[0]
    return value / gamma(alpha + 1.0)


# ---------------------------------------------------------------------------
# 3. Infinite products and the exact log-periodic fractional defect
# ---------------------------------------------------------------------------

mp.mp.dps = 70
LOG2 = mp.log(2)


def up_mgf(s: mp.mpf) -> mp.mpf:
    """M_up(s)=prod_{k>=1} sinh(s/2^k)/(s/2^k)."""
    s = mp.mpf(s)
    product = mp.mpf(1)
    for k in range(1, 300):
        z = s / (2**k)
        product *= mp.sinh(z) / z if z else 1
        if abs(z) < mp.mpf("1e-55"):
            break
    return product


def thue_morse_laplace_product(s: mp.mpf) -> mp.mpf:
    """T(s)=prod_{j>=0}(1-exp(-2^{j+1}s))."""
    s = mp.mpf(s)
    product = mp.mpf(1)
    for j in range(0, 400):
        z = mp.power(2, j + 1) * s
        product *= 1 - mp.e ** (-z)
        if mp.e ** (-z) < mp.mpf("1e-60"):
            break
    return product


def signed_extension_laplace(s: mp.mpf) -> mp.mpf:
    """Laplace transform of the signed global extension mathcal F.

      L(s)=e^{-s} M_up(s) prod_{j>=0}(1-e^{-2^{j+1}s}).
    """
    s = mp.mpf(s)
    return mp.e ** (-s) * up_mgf(s) * thue_morse_laplace_product(s)


def periodic_P(u: mp.mpf) -> mp.mpf:
    """Exact one-periodic correction P(u) obtained from L(s/2)=sL(s)."""
    u = mp.mpf(u)
    s = mp.power(2, u)
    return mp.log(signed_extension_laplace(s)) + LOG2 * (u * u + u) / 2


def dilation_transform_ratio(alpha: mp.mpf, s: mp.mpf) -> mp.mpf:
    """Laplace-transform ratio A_alpha/I^alpha for the global extension.

    A_alpha f(x)=2^{alpha(alpha-1)/2} f(x/2^alpha).
    The exact theorem gives

      ratio = exp(P(log_2 s + alpha)-P(log_2 s)).
    """
    alpha = mp.mpf(alpha)
    s = mp.mpf(s)
    u = mp.log(s, 2)
    return mp.e ** (periodic_P(u + alpha) - periodic_P(u))


def sinc_product(t: float, terms: int = 64) -> float:
    """Fourier transform of up in the convention exp(-itx)."""
    product = 1.0
    for k in range(1, terms + 1):
        z = t / (2**k)
        product *= math.sin(z) / z if z else 1.0
    return product


def up_value(x: float) -> float:
    """Approximate up(x)=F(1-|x|) on [-1,1]."""
    ax = abs(x)
    return F_APPROX(1.0 - ax) if ax <= 1.0 else 0.0


def fractional_laplacian_constant(alpha: float) -> float:
    """C_{1,alpha} for Fourier multiplier |xi|^alpha, 0<alpha<2."""
    return float(
        (2**alpha)
        * mp.gamma((1 + alpha) / 2)
        / (mp.sqrt(mp.pi) * abs(mp.gamma(-alpha / 2)))
    )


def fractional_laplacian_tail_series(alpha: float, x: float, terms: int) -> float:
    """Moment expansion outside support for (-Delta)^(alpha/2) up(x)."""
    c = mp.mpf(fractional_laplacian_constant(alpha))
    total = mp.mpf(0)
    for j in range(terms):
        moment = mp.mpf(str(sp.N(MZ_EXACT[2 * j], 60)))
        total += (
            mp.rf(1 + alpha, 2 * j)
            / mp.factorial(2 * j)
            * moment
            * mp.power(x, -1 - alpha - 2 * j)
        )
    return float(-c * total)


# ---------------------------------------------------------------------------
# 4. Tables, checks, and figures
# ---------------------------------------------------------------------------

def write_moment_table(path: Path) -> None:
    rows = []
    for n in range(0, 11):
        centered = MZ_EXACT[n] if n < len(MZ_EXACT) else sp.Integer(0)
        rows.append(
            f"{n} & ${sp.latex(MU_EXACT[n])}$ & ${sp.latex(centered)}$ \\\\"
        )
    path.write_text(
        "\\begin{tabular}{@{}rll@{}}\n"
        "\\toprule\n"
        "$n$ & $\\mu_n=\\mathbb E(Y^n)$ & $m_n=\\mathbb E(Z^n)$ \\\\ \n"
        "\\midrule\n"
        + "\n".join(rows)
        + "\n\\bottomrule\n\\end{tabular}\n",
        encoding="utf-8",
    )


def make_fractional_dilation_figure(path: Path) -> None:
    # A slightly cheaper spline is sufficient for a qualitative plot.
    F_plot = FabiusSplineApproximation(level=10)
    xs = np.linspace(0.03, 1.0, 95)
    for alpha in (0.25, 0.50, 0.75):
        defects = []
        for x in xs:
            j = rl_integral_F(alpha, float(x), F=F_plot)
            a = 2 ** (alpha * (alpha - 1) / 2) * F_plot(float(x) / 2**alpha)
            defects.append(1e3 * (j - a))
        plt.plot(xs, defects, label=rf"$\alpha={alpha:.2f}$")
    plt.axhline(0.0, linewidth=0.8)
    plt.xlabel(r"$x$")
    plt.ylabel(r"$10^3\,[I_{0+}^{\alpha}F(x)-A_{\alpha}F(x)]$")
    plt.title(r"Physical-space fractional dilation defect on $0<x\leq1$")
    plt.legend()
    plt.tight_layout()
    plt.savefig(path, dpi=220)
    plt.close()


def make_periodic_defect_figure(path: Path) -> None:
    grid = np.linspace(0.0, 1.0, 257)
    values = np.array([float(periodic_P(mp.mpf(u))) for u in grid])
    # Numerical trapezoidal mean; endpoint duplicated, so omit the last sample.
    mean = float(np.mean(values[:-1]))
    psi_ppm = 1e6 * (values - mean)
    log_ratio_ppm = np.array(
        [1e6 * float(mp.log(dilation_transform_ratio(mp.mpf("0.5"), mp.power(2, u)))) for u in grid]
    )
    plt.plot(grid, psi_ppm, label=r"$10^6\Psi(u)$")
    plt.plot(grid, log_ratio_ppm, label=r"$10^6\log R_{1/2}(2^u)$")
    plt.xlabel(r"$u=\log_2 s$")
    plt.ylabel("parts per million")
    plt.title("Gamma-zeta oscillation and the half-order transform defect")
    plt.legend()
    plt.tight_layout()
    plt.savefig(path, dpi=220)
    plt.close()


def format_float(x: float, digits: int = 12) -> str:
    return f"{x:.{digits}g}"


def run_checks() -> str:
    lines: list[str] = []
    lines.append("REPRODUCIBLE NUMERICAL CHECKS")
    lines.append("================================")
    lines.append(f"Finite spline level N = {F_APPROX.level}")
    lines.append("")

    lines.append("1. Exact moments generated from Bernoulli cumulants")
    for n in range(0, 11):
        lines.append(f"  mu_{n:2d} = {MU_EXACT[n]}")
    lines.append("")

    lines.append("2. Ordinary primitive F(x/2)=int_0^x F(t) dt")
    for x in (0.25, 0.50, 0.80, 1.00):
        integral = quad(F_APPROX, 0.0, x, epsabs=2e-10, epsrel=2e-10, limit=250)[0]
        rhs = F_APPROX(x / 2.0)
        lines.append(
            f"  x={x:4.2f}: integral={integral:.12g}, F(x/2)={rhs:.12g}, error={integral-rhs:+.3e}"
        )
    lines.append("")

    lines.append("3. Fractional order-shift J_{a+1}(x)=2^a J_a(x/2)")
    for alpha, x in ((0.37, 0.40), (0.37, 0.80), (0.63, 0.70)):
        lhs = rl_integral_F(alpha + 1.0, x)
        rhs = 2**alpha * rl_integral_F(alpha, x / 2.0)
        lines.append(
            f"  a={alpha:.2f}, x={x:.2f}: lhs={lhs:.12g}, rhs={rhs:.12g}, error={lhs-rhs:+.3e}"
        )
    lines.append("")

    lines.append("4. Fractional dyadic moment formula")
    lines.append("   J_beta(2^-n)=2^{-n beta-n(n-1)/2} mu(n+beta)/Gamma(n+beta+1)")
    for beta, n in ((0.37, 2), (0.50, 3), (0.73, 2)):
        lhs = rl_integral_F(beta, 2.0 ** (-n))
        rhs = (
            2 ** (-n * beta - n * (n - 1) / 2)
            * mu_numeric(n + beta)
            / gamma(n + beta + 1)
        )
        lines.append(
            f"  beta={beta:.2f}, n={n}: lhs={lhs:.12g}, rhs={rhs:.12g}, error={lhs-rhs:+.3e}"
        )
    lines.append("")

    lines.append("5. Quantile fractional-transmutation formula")
    for alpha, y in ((0.60, 0.30), (0.40, 0.70), (0.75, 0.50)):
        direct = rl_integral_inverse_direct(alpha, y)
        trans = rl_integral_inverse_transmuted(alpha, y)
        lines.append(
            f"  a={alpha:.2f}, y={y:.2f}: direct={direct:.12g}, transmuted={trans:.12g}, error={direct-trans:+.3e}"
        )
    lines.append("")

    lines.append("6. Mixed product integral and its sinc-product representation")
    direct_product = quad(
        lambda x: F_APPROX(x) * (1.0 - F_APPROX(x)),
        0.0,
        1.0,
        epsabs=2e-10,
        epsrel=2e-10,
        limit=300,
    )[0]
    # Formula: I=(1/(2*pi))*int_0^infty (1-P(t)^2)/t^2 dt.
    # Above T=100, P(t)^2 is negligible at the displayed precision and the
    # remaining integral of 1/t^2 is exactly 1/T.
    T = 100.0
    fourier_value = (
        quad(
            lambda t: (1.0 - sinc_product(t) ** 2) / (t * t) if t else 1.0 / 9.0,
            0.0,
            T,
            epsabs=2e-10,
            epsrel=2e-10,
            limit=700,
        )[0]
        + 1.0 / T
    ) / (2.0 * math.pi)
    lines.append(f"  direct integral = {direct_product:.12g}")
    lines.append(f"  sinc integral   = {fourier_value:.12g}")
    lines.append(f"  difference      = {direct_product-fourier_value:+.3e}")
    lines.append("")

    lines.append("7. Sobolev/fractional energies E_a=(1/pi) int_0^infty t^a P(t)^2 dt")
    for alpha in (0.0, 0.5, 1.0, 2.0, 4.0):
        bounds = (0.0, 10.0, 30.0, 100.0, 300.0)
        energy = 0.0
        for left, right in zip(bounds[:-1], bounds[1:]):
            energy += quad(
                lambda t: (t**alpha) * sinc_product(t) ** 2,
                left,
                right,
                epsabs=2e-10,
                epsrel=2e-9,
                limit=900,
            )[0]
        energy /= math.pi
        lines.append(f"  E_{alpha:g} = {energy:.12g}")
    lines.append("")

    lines.append("8. Fractional-Laplacian tail series at x=2")
    for alpha in (0.5, 0.7, 1.3):
        c = fractional_laplacian_constant(alpha)
        direct = -c * quad(
            lambda t: up_value(t) / (2.0 - t) ** (1.0 + alpha),
            -1.0,
            1.0,
            epsabs=2e-10,
            epsrel=2e-10,
            limit=300,
        )[0]
        partial = fractional_laplacian_tail_series(alpha, 2.0, terms=6)
        lines.append(
            f"  a={alpha:.1f}: direct={direct:.12g}, six terms={partial:.12g}, error={direct-partial:+.3e}"
        )
    lines.append("")

    lines.append("9. Exact Gamma-zeta fractional defect in Laplace space")
    for alpha in (0.25, 0.50, 0.75, 1.00, 1.50):
        values = [dilation_transform_ratio(mp.mpf(alpha), mp.mpf(s)) for s in (0.1, 1.0, 10.0)]
        values_text = ", ".join(mp.nstr(v, 18) for v in values)
        lines.append(f"  alpha={alpha:4.2f}: R_alpha(0.1,1,10) = {values_text}")
    lines.append("  The equality R_{alpha+1}=R_alpha is exact; R_n=1 for every integer n.")
    lines.append("")

    grid = [mp.mpf(i) / 512 for i in range(513)]
    pvals = [periodic_P(u) for u in grid]
    amplitude = max(pvals) - min(pvals)
    lines.append("10. Periodic correction amplitude")
    lines.append(f"  peak-to-peak P = {mp.nstr(amplitude, 18)}")
    lines.append("  (The first Gamma-zeta Fourier mode accounts for essentially all of it.)")

    return "\n".join(lines) + "\n"


def main() -> None:
    write_moment_table(HERE / "moment_table.tex")
    (HERE / "numerical_results.txt").write_text(run_checks(), encoding="utf-8")
    make_fractional_dilation_figure(HERE / "fractional_dilation_defect.png")
    make_periodic_defect_figure(HERE / "gamma_zeta_fractional_defect.png")
    print(f"Wrote outputs to {HERE}")


if __name__ == "__main__":
    main()
