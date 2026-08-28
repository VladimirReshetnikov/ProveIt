#!/usr/bin/env python3
r"""
Numerical experiments for

  Fractional Quantile Transmutation, Complex-Order Resolvents,
  and Nonlocal Rvachev Calculus

The script reconstructs Rvachev's up-function from its Fourier product,
builds the Fabius distribution and inverse distribution numerically, and
checks the identities developed in the accompanying report.

Conventions
-----------
* Fourier transform:  f^(xi) = integral exp(-i xi x) f(x) dx.
* sinc(z) = sin(z)/z.
* up^(xi) = product_{j>=1} sinc(xi/2^j).
* If Y has density up on [-1,1], then X=(Y+1)/2 has CDF F on [0,1].
* G=F^{-1} is the ordinary inverse on (0,1).
* The normalized positive-part hierarchy is
      K_beta(a) = E[(D-a)_+^beta] / Gamma(beta+1),
  D=X_2-X_1.
  This Gamma normalization is essential: it gives
      -d/da K_beta = K_{beta-1}.

The calculations are deterministic.  They use only NumPy, SciPy, mpmath,
and Matplotlib.  The default grid N=2^17 provides roughly 10-12 digits for
smooth bulk integrals and 7-9 digits for the deliberately singular boundary
checks.  Command-line option --quick reduces N for a faster smoke test.

Outputs
-------
* numerical_results.txt  human-readable transcript
* numerical_results.tex  LaTeX tables included by the report
* figure_quantile_fractional.pdf/.png
* figure_stieltjes_convergence.pdf/.png
* figure_difference_hierarchy.pdf/.png
* figure_nonlocal_tails.pdf/.png

Run from this directory, for example:

    python numerical_experiments.py

The code avoids relying on any tabulated Fabius values except when it prints
an independent diagnostic comparison with F(1/4)=5/72.
"""

from __future__ import annotations

import argparse
import cmath
import os
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable

os.environ.setdefault("TERM", "dumb")

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.integrate import cumulative_trapezoid, quad
from scipy.interpolate import PchipInterpolator
from scipy.signal import fftconvolve
from scipy.special import gamma, gammaln, poch


# More precision is useful for the one-dimensional reference quadratures.
mp.mp.dps = 50


@dataclass
class FabiusGrid:
    """Uniform-grid numerical representation of up, F, and G."""

    y: np.ndarray
    up: np.ndarray
    dy: float
    x: np.ndarray
    F: np.ndarray
    G_u: np.ndarray
    G: np.ndarray
    up_interp: PchipInterpolator
    F_interp: PchipInterpolator
    G_interp: PchipInterpolator


@dataclass
class DifferenceGrid:
    """Density h of D=X_2-X_1 on a uniform grid."""

    a: np.ndarray
    h: np.ndarray
    da: float
    h_interp: PchipInterpolator


@dataclass
class Check:
    name: str
    lhs: complex
    rhs: complex

    @property
    def abs_error(self) -> float:
        return float(abs(self.lhs - self.rhs))

    @property
    def rel_error(self) -> float:
        scale = max(abs(self.lhs), abs(self.rhs), 1.0e-300)
        return float(abs(self.lhs - self.rhs) / scale)


def sinc(z: np.ndarray) -> np.ndarray:
    """sin(z)/z, with the removable value at zero supplied by NumPy."""

    return np.sinc(z / np.pi)


def reconstruct_fabius_grid(N: int = 2**17, L: float = 4.0, J: int = 35) -> FabiusGrid:
    r"""Reconstruct up by inverse FFT and derive F and G.

    The spatial interval [-L/2,L/2) is larger than the support [-1,1], so
    periodic wrap-around does not contaminate the supported function.  The
    phase exp(-i*pi*k) shifts the inverse-FFT origin to -L/2.
    """

    if N & (N - 1):
        raise ValueError("N must be a power of two")
    if L <= 2.0:
        raise ValueError("L must exceed the support width 2")

    k = np.fft.fftfreq(N) * N
    omega = 2.0 * np.pi * k / L
    up_hat = np.ones(N, dtype=np.float64)
    for j in range(1, J + 1):
        up_hat *= sinc(omega / (2.0**j))

    phase = np.exp(-1j * np.pi * k)
    up = np.fft.ifft((N / L) * up_hat * phase).real
    up[np.abs(up) < 5.0e-15] = 0.0

    dy = L / N
    y = -L / 2.0 + np.arange(N) * dy

    # Restrict to the exact support, enforce the analytically known endpoints,
    # and renormalize only by the tiny floating-point mass defect.
    support = (y >= -1.0) & (y <= 1.0)
    ys = y[support]
    us = np.maximum(up[support], 0.0)
    mass = np.trapezoid(us, ys)
    us /= mass

    # X=(Y+1)/2.  The x-grid therefore has spacing dy/2.
    x = (ys + 1.0) / 2.0
    F = cumulative_trapezoid(us, ys, initial=0.0)
    F /= F[-1]
    F[0], F[-1] = 0.0, 1.0

    # PCHIP preserves monotonicity and avoids oscillations in the extremely flat
    # endpoint regions.  Remove any duplicate floating-point CDF ordinates
    # before constructing the inverse interpolation.
    F_unique, idx = np.unique(F, return_index=True)
    x_unique = x[idx]
    if F_unique[0] != 0.0:
        F_unique = np.insert(F_unique, 0, 0.0)
        x_unique = np.insert(x_unique, 0, 0.0)
    if F_unique[-1] != 1.0:
        F_unique = np.append(F_unique, 1.0)
        x_unique = np.append(x_unique, 1.0)

    up_interp = PchipInterpolator(ys, us, extrapolate=False)
    F_interp = PchipInterpolator(x, F, extrapolate=False)
    G_interp = PchipInterpolator(F_unique, x_unique, extrapolate=False)

    # A logarithmically enriched u-grid is convenient for plots and endpoint
    # diagnostics.  It is not used as the sole source for quadrature.
    u_left = np.geomspace(1.0e-12, 1.0e-2, 500, endpoint=False)
    u_bulk = np.linspace(1.0e-2, 1.0 - 1.0e-2, 1600, endpoint=True)
    u_right = 1.0 - u_left[::-1]
    G_u = np.unique(np.concatenate(([0.0], u_left, u_bulk, u_right, [1.0])))
    G = G_interp(G_u)
    G[0], G[-1] = 0.0, 1.0

    return FabiusGrid(
        y=ys,
        up=us,
        dy=dy,
        x=x,
        F=F,
        G_u=G_u,
        G=G,
        up_interp=up_interp,
        F_interp=F_interp,
        G_interp=G_interp,
    )


def standard_moments(nmax: int) -> list[Fraction]:
    """Exact moments d_n=E[X^n] from X=(U+X')/2."""

    d = [Fraction(1)]
    for n in range(1, nmax + 1):
        numerator = sum(
            Fraction(math.comb(n, k), n - k + 1) * d[k]
            for k in range(n)
        )
        d.append(numerator / (2**n - 1))
    return d


def centered_moments(nmax: int) -> list[Fraction]:
    """Exact moments c_n=E[Y^(2n)] from Y=(V+Y')/2."""

    c = [Fraction(1)]
    for n in range(1, nmax + 1):
        numerator = sum(
            Fraction(math.comb(2 * n + 1, 2 * k)) * c[k]
            for k in range(n)
        )
        denominator = (2 * n + 1) * (4**n - 1)
        c.append(numerator / denominator)
    return c


def quad_real_or_complex(
    func: Callable[[float], complex], a: float, b: float, **kwargs: float
) -> complex:
    """SciPy quad wrapper that integrates real and imaginary parts separately."""

    real = quad(lambda t: float(np.real(func(t))), a, b, **kwargs)[0]
    imag = quad(lambda t: float(np.imag(func(t))), a, b, **kwargs)[0]
    return complex(real, imag)


def rl_quantile_direct(grid: FabiusGrid, u: float, beta: float, p: complex) -> complex:
    r"""Direct Riemann--Liouville integral of G(v)^p in the u-variable."""

    q = float(grid.G_interp(u))

    # v=u(1-s) removes the upper endpoint from a fixed interval.  quad handles
    # the algebraic weight at s=0 directly.
    def integrand(s: float) -> complex:
        v = u * (1.0 - s)
        gv = float(grid.G_interp(max(v, 0.0)))
        if gv == 0.0:
            return 0.0j
        return (s ** (beta - 1.0)) * cmath.exp(p * math.log(gv))

    integral = quad_real_or_complex(integrand, 0.0, 1.0, epsabs=2e-12, epsrel=2e-12, limit=400)
    return (u**beta) * integral / gamma(beta)


def rl_quantile_transmuted(grid: FabiusGrid, u: float, beta: float, p: complex) -> complex:
    r"""Transmuted x-integral for I^beta G^p, initially Re(p)>0."""

    q = float(grid.G_interp(u))

    def integrand(x: float) -> complex:
        if x == 0.0:
            return 0.0j
        kernel = max(u - float(grid.F_interp(x)), 0.0) ** beta
        return cmath.exp((p - 1.0) * math.log(x)) * kernel

    integral = quad_real_or_complex(integrand, 0.0, q, epsabs=2e-12, epsrel=2e-12, limit=500)
    return p * integral / gamma(beta + 1.0)


def rl_quantile_regularized(grid: FabiusGrid, u: float, beta: float, p: complex) -> complex:
    r"""Entire continuation in p of the transmuted power formula."""

    q = float(grid.G_interp(u))
    u_beta = u**beta

    def integrand(x: float) -> complex:
        if x == 0.0:
            return 0.0j
        kernel_difference = max(u - float(grid.F_interp(x)), 0.0) ** beta - u_beta
        return cmath.exp((p - 1.0) * math.log(x)) * kernel_difference

    integral = quad_real_or_complex(integrand, 0.0, q, epsabs=3e-12, epsrel=3e-12, limit=500)
    return (u_beta * cmath.exp(p * math.log(q)) + p * integral) / gamma(beta + 1.0)


def rl_log_direct(grid: FabiusGrid, u: float, beta: float, m: int) -> float:
    """Direct Riemann--Liouville integral of (log G)^m."""

    def integrand(s: float) -> float:
        v = u * (1.0 - s)
        gv = float(grid.G_interp(max(v, 0.0)))
        if gv <= 0.0:
            return 0.0
        return (s ** (beta - 1.0)) * (math.log(gv) ** m)

    integral = quad(integrand, 0.0, 1.0, epsabs=3e-12, epsrel=3e-12, limit=500)[0]
    return (u**beta) * integral / gamma(beta)


def rl_log_transmuted(grid: FabiusGrid, u: float, beta: float, m: int) -> float:
    """Derivative-at-p=0 form of the entire continuation."""

    q = float(grid.G_interp(u))
    u_beta = u**beta

    if m == 0:
        return u_beta / gamma(beta + 1.0)

    def integrand(x: float) -> float:
        if x == 0.0:
            return 0.0
        diff = max(u - float(grid.F_interp(x)), 0.0) ** beta - u_beta
        return (math.log(x) ** (m - 1)) * diff / x

    integral = quad(integrand, 0.0, q, epsabs=3e-12, epsrel=3e-12, limit=600)[0]
    return (u_beta * math.log(q) ** m + m * integral) / gamma(beta + 1.0)


def caputo_direct(grid: FabiusGrid, u: float, alpha: float, p: float) -> float:
    r"""Direct Caputo value in a cancellation-safe Marchaud form.

    For f(0)=0 and 0<alpha<1,

        C D^alpha f(u) = u^(-alpha)/Gamma(1-alpha)
            [f(u) + alpha integral_0^1
             (f(u)-f(u(1-s))) s^(-alpha-1) ds].

    This check uses only values of G and is therefore numerically independent
    of the x-variable transmutation.
    """

    q = float(grid.G_interp(u))
    fu = q**p
    density_q = 2.0 * float(grid.up_interp(2.0 * q - 1.0))
    endpoint_limit = u * p * q ** (p - 1.0) / density_q

    def regular_part(s: float) -> float:
        # (f(u)-f(u(1-s)))/s has the finite limit u f'(u).
        if s == 0.0:
            return endpoint_limit
        v = u * (1.0 - s)
        fv = 0.0 if v <= 0.0 else float(grid.G_interp(v)) ** p
        return (fu - fv) / s

    integral = quad(
        regular_part,
        0.0,
        1.0,
        weight="alg",
        wvar=(-alpha, 0.0),
        epsabs=2e-10,
        epsrel=2e-10,
        limit=500,
    )[0]
    return u ** (-alpha) * (fu + alpha * integral) / gamma(1.0 - alpha)


def caputo_transmuted(grid: FabiusGrid, u: float, alpha: float, p: float) -> float:
    r"""Exact x-variable transmutation of the Caputo derivative.

    The substitution q-x=q*s^(1/(1-alpha)) analytically cancels the
    endpoint singularity (u-F(x))^(-alpha).
    """

    q = float(grid.G_interp(u))
    exponent = 1.0 / (1.0 - alpha)
    fprime_q = 2.0 * float(grid.up_interp(2.0 * q - 1.0))

    def integrand(s: float) -> float:
        if s == 0.0:
            # Limit obtained from u-F(x) ~ F'(q)(q-x).
            return p * exponent * q**p * (fprime_q * q) ** (-alpha)
        power = s**exponent
        x = q * (1.0 - power)
        dx_ds = q * exponent * s ** (exponent - 1.0)
        if x <= 0.0:
            x_power = 1.0 if p == 1.0 else 0.0
        else:
            x_power = x ** (p - 1.0)
        if power < 1.0e-6:
            # Direct subtraction loses relative precision this close to q.
            delta = fprime_q * q * power
        else:
            delta = u - float(grid.F_interp(x))
            if delta <= 0.0:
                delta = fprime_q * q * power
        return p * x_power * delta ** (-alpha) * dx_ds

    val = quad(integrand, 0.0, 1.0, epsabs=2e-9, epsrel=2e-9, limit=500)[0]
    return val / gamma(1.0 - alpha)


def generalized_stieltjes_density(
    grid: FabiusGrid, z: complex, lam: complex
) -> complex:
    """S_lambda(z)=integral (z-x)^(-lambda) dF(x)."""

    density = 2.0 * grid.up
    values = np.exp(-lam * np.log(z - grid.x))
    return complex(np.trapezoid(values * density, grid.x))


def generalized_stieltjes_moment_series(
    z: complex, lam: complex, moments: list[Fraction], terms: int
) -> complex:
    """Truncated moment expansion of S_lambda for |z|>1."""

    total = 0.0j
    for n in range(terms):
        coeff = complex(mp.rf(lam, n) / mp.factorial(n))
        total += coeff * float(moments[n]) / (z**n)
    return cmath.exp(-lam * cmath.log(z)) * total


def generalized_stieltjes_derivative_density(
    grid: FabiusGrid, z: complex, lam: complex
) -> complex:
    """Differentiate S_lambda under the integral sign."""

    density = 2.0 * grid.up
    values = -lam * np.exp(-(lam + 1.0) * np.log(z - grid.x))
    return complex(np.trapezoid(values * density, grid.x))


def boundary_jump_reference(grid: FabiusGrid, x0: float, lam: float) -> complex:
    """Predicted generalized-Stieltjes boundary jump."""

    def integrand(t: float) -> float:
        density = 2.0 * float(grid.up_interp(2.0 * t - 1.0))
        return (t - x0) ** (-lam) * density

    val = quad(integrand, x0, 1.0, epsabs=2e-11, epsrel=2e-11, limit=800, points=[x0])[0]
    return -2j * math.sin(math.pi * lam) * val


def weyl_left_tail_direct(grid: FabiusGrid, x: float, alpha: float) -> float:
    """Left Weyl derivative outside the support, x>1, 0<alpha<1."""

    val = np.trapezoid(grid.up * (x - grid.y) ** (-1.0 - alpha), grid.y)
    return float(val / gamma(-alpha))


def weyl_left_tail_series(
    x: float, alpha: float, centered: list[Fraction], terms: int
) -> float:
    """Moment expansion of the left Weyl tail."""

    total = 0.0
    for j in range(terms):
        coeff = float(mp.rf(alpha + 1.0, 2 * j) / mp.factorial(2 * j))
        total += coeff * float(centered[j]) / (x ** (2 * j))
    return float(x ** (-1.0 - alpha) * total / gamma(-alpha))


def riesz_tail_direct(grid: FabiusGrid, x: float, alpha: float) -> float:
    """Fractional-Laplacian tail outside [-1,1]."""

    C_alpha = gamma(1.0 + alpha) * math.sin(math.pi * alpha / 2.0) / math.pi
    val = np.trapezoid(grid.up * np.abs(x - grid.y) ** (-1.0 - alpha), grid.y)
    return float(-C_alpha * val)


def difference_grid(grid: FabiusGrid) -> DifferenceGrid:
    r"""Compute h, the density of D=X_2-X_1, by FFT convolution.

    The X-density is f(x)=2 up(2x-1).  Since it is symmetric about 1/2,
    correlation and convolution with the reversed vector coincide.
    """

    f = 2.0 * grid.up
    dx = grid.x[1] - grid.x[0]
    h = fftconvolve(f, f[::-1], mode="full") * dx
    a = np.arange(-(len(f) - 1), len(f)) * dx
    h = np.maximum(h, 0.0)
    h /= np.trapezoid(h, a)
    return DifferenceGrid(a=a, h=h, da=dx, h_interp=PchipInterpolator(a, h, extrapolate=False))


def K_beta(diff: DifferenceGrid, a0: float, beta: float) -> float:
    """Gamma-normalized positive-part moment K_beta(a0)."""

    mask = diff.a >= a0
    t = diff.a[mask] - a0
    vals = np.zeros_like(t)
    positive = t > 0.0
    vals[positive] = t[positive] ** beta * diff.h[mask][positive]
    return float(np.trapezoid(vals, diff.a[mask]) / gamma(beta + 1.0))



def K_beta_quad(diff: DifferenceGrid, a0: float, beta: float) -> float:
    r"""High-accuracy quadrature for K_beta(a0), beta>-1.

    A Gauss--Jacobi weighted rule handles the t^beta endpoint exactly enough
    that this routine is preferable for the reported identity checks.  The
    vectorized trapezoidal K_beta above remains useful for plotting.
    """

    if a0 >= 1.0:
        return 0.0
    lower = max(a0, -1.0)
    width = 1.0 - lower
    shift = lower - a0

    # When a0 lies inside the support, shift=0 and the algebraic singularity
    # is at s=0.  If a0<-1, the integrand is smooth and ordinary quad is used.
    if abs(shift) < 1.0e-15:
        weighted = quad(
            lambda s: float(diff.h_interp(lower + width * s)),
            0.0,
            1.0,
            weight="alg",
            wvar=(beta, 0.0),
            epsabs=2e-11,
            epsrel=2e-11,
            limit=300,
        )[0]
        integral = width ** (beta + 1.0) * weighted
    else:
        integral = quad(
            lambda d: (d - a0) ** beta * float(diff.h_interp(d)),
            lower,
            1.0,
            epsabs=2e-11,
            epsrel=2e-11,
            limit=300,
        )[0]
    return float(integral / gamma(beta + 1.0))

def K_beta_refined(diff: DifferenceGrid, a0: float, beta: float) -> float:
    """High-accuracy right side of the triangular refinement equation."""

    # Fixed Gauss--Legendre quadrature on each side of the cusp at v=0.
    nodes, weights = np.polynomial.legendre.leggauss(72)
    total = 0.0
    for left, right in [(-1.0, 0.0), (0.0, 1.0)]:
        v = 0.5 * (right - left) * nodes + 0.5 * (right + left)
        w = 0.5 * (right - left) * weights
        values = np.array([
            (1.0 - abs(float(vj))) * K_beta_quad(diff, 2.0 * a0 - float(vj), beta)
            for vj in v
        ])
        total += float(np.dot(w, values))
    return (2.0 ** (-beta)) * total


def K_even_exact(n: int, centered: list[Fraction]) -> Fraction:
    """Exact K_{2n}(0), including the Gamma normalization."""

    moment_D = Fraction(1, 4**n) * sum(
        Fraction(math.comb(2 * n, 2 * k)) * centered[k] * centered[n - k]
        for k in range(n + 1)
    )
    return moment_D / (2 * math.factorial(2 * n))


def fractional_energy_fourier(
    grid: FabiusGrid, centered: list[Fraction], beta: float
) -> float:
    r"""Fourier formula for K_beta(0), 0<beta<2.

    Near the origin, direct evaluation of 1-phi_D(t) suffers catastrophic
    cancellation.  We therefore use exact even moments of D for |t|<0.04
    and the infinite sinc product outside that interval.
    """

    t = np.geomspace(1.0e-10, 1.0e5, 220000)
    omega = t / 2.0
    phi_y = np.ones_like(omega)
    for j in range(1, 46):
        phi_y *= sinc(omega / (2.0**j))
    one_minus = 1.0 - phi_y**2

    # Exact moments of D=(Y_2-Y_1)/2.
    d_even: list[float] = [1.0]
    for n in range(1, 8):
        mu = Fraction(1, 4**n) * sum(
            Fraction(math.comb(2 * n, 2 * k)) * centered[k] * centered[n - k]
            for k in range(n + 1)
        )
        d_even.append(float(mu))

    small = t < 0.04
    ts = t[small]
    series = np.zeros_like(ts)
    for n in range(1, len(d_even)):
        series += ((-1.0) ** (n + 1)) * d_even[n] * ts ** (2 * n) / math.factorial(2 * n)
    one_minus[small] = series

    integrand = one_minus / (t ** (1.0 + beta))
    integral = np.trapezoid(integrand, t)

    t0 = t[0]
    integral += (d_even[1] / 2.0) * t0 ** (2.0 - beta) / (2.0 - beta)
    # Since phi_D decays faster than every power, the omitted far tail is
    # integral_{t1}^infinity t^{-1-beta} dt to beyond displayed precision.
    t1 = t[-1]
    integral += t1 ** (-beta) / beta

    return float(math.sin(math.pi * beta / 2.0) * integral / math.pi)


def endpoint_ratio(grid: FabiusGrid, u: float, beta: float, p: float) -> float:
    """Ratio testing I^beta G^p ~ u^beta G(u)^p/Gamma(beta+1)."""

    value = rl_quantile_direct(grid, u, beta, p)
    q = float(grid.G_interp(u))
    leading = u**beta * q**p / gamma(beta + 1.0)
    return float(np.real(value / leading))


def make_figures(
    out: Path,
    grid: FabiusGrid,
    diff: DifferenceGrid,
    moments: list[Fraction],
    centered: list[Fraction],
) -> None:
    """Generate four standalone figures (no subplots)."""

    # 1. Quantile and two fractional operators.
    u = np.linspace(0.002, 0.998, 260)
    Gvals = grid.G_interp(u)
    Ihalf = np.array([rl_quantile_transmuted(grid, float(v), 0.5, 1.0).real for v in u])
    Chalf = np.array([caputo_transmuted(grid, float(v), 0.5, 1.0) for v in u])
    plt.figure(figsize=(7.2, 4.6))
    plt.plot(u, Gvals, label=r"$G(u)$")
    plt.plot(u, Ihalf, label=r"$I_{0+}^{1/2}G(u)$")
    plt.plot(u, Chalf, label=r"${}^{C}D_{0+}^{1/2}G(u)$")
    plt.xlabel(r"$u$")
    plt.ylabel("value")
    plt.title("Inverse Fabius function and half-order operators")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out / "figure_quantile_fractional.pdf")
    plt.savefig(out / "figure_quantile_fractional.png", dpi=180)
    plt.close()

    # 2. Moment-series convergence for the generalized Stieltjes transform.
    cases = [(2.2 + 0j, 1.4 + 0j), (1.7 + 0.4j, 0.6 + 0.3j)]
    plt.figure(figsize=(7.2, 4.6))
    term_counts = np.arange(2, 41)
    for z, lam in cases:
        exact = generalized_stieltjes_density(grid, z, lam)
        errors = [
            abs(generalized_stieltjes_moment_series(z, lam, moments, int(n)) - exact)
            for n in term_counts
        ]
        plt.semilogy(term_counts, errors, marker="o", markersize=2.5, label=fr"$z={z},\ \lambda={lam}$")
    plt.xlabel("number of moment terms")
    plt.ylabel("absolute error")
    plt.title("Generalized Stieltjes moment-series convergence")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out / "figure_stieltjes_convergence.pdf")
    plt.savefig(out / "figure_stieltjes_convergence.png", dpi=180)
    plt.close()

    # 3. Entire-order positive-part hierarchy on the real order axis.
    a = np.linspace(-0.96, 0.96, 500)
    plt.figure(figsize=(7.2, 4.6))
    plt.plot(diff.a, diff.h, label=r"$K_{-1}(a)=h(a)$")
    for beta in [0.0, 0.5, 1.0]:
        vals = np.array([K_beta(diff, float(v), beta) for v in a])
        plt.plot(a, vals, label=fr"$K_{{{beta:g}}}(a)$")
    plt.xlim(-1.0, 1.0)
    plt.xlabel(r"threshold $a$")
    plt.ylabel("Gamma-normalized value")
    plt.title("Difference-distribution order ladder")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out / "figure_difference_hierarchy.pdf")
    plt.savefig(out / "figure_difference_hierarchy.png", dpi=180)
    plt.close()

    # 4. Algebraic tails created by nonlocal differentiation.
    x = np.geomspace(1.02, 12.0, 300)
    alpha_w, alpha_r = 0.6, 1.2
    weyl = np.array([-weyl_left_tail_direct(grid, float(v), alpha_w) for v in x])
    riesz = np.array([-riesz_tail_direct(grid, float(v), alpha_r) for v in x])
    lead_w = -np.array([xv ** (-1.0 - alpha_w) / gamma(-alpha_w) for xv in x])
    C_r = gamma(1.0 + alpha_r) * math.sin(math.pi * alpha_r / 2.0) / math.pi
    lead_r = C_r * x ** (-1.0 - alpha_r)
    plt.figure(figsize=(7.2, 4.6))
    plt.loglog(x, weyl, label=fr"$-D_+^{{{alpha_w}}}\,\mathrm{{up}}(x)$")
    plt.loglog(x, lead_w, linestyle="--", label="Weyl leading term")
    plt.loglog(x, riesz, label=fr"$-(-\Delta)^{{{alpha_r}/2}}\,\mathrm{{up}}(x)$")
    plt.loglog(x, lead_r, linestyle="--", label="Riesz leading term")
    plt.xlabel(r"$x>1$")
    plt.ylabel("tail magnitude")
    plt.title("Nonlocal fractional derivatives destroy compact support")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out / "figure_nonlocal_tails.pdf")
    plt.savefig(out / "figure_nonlocal_tails.png", dpi=180)
    plt.close()


def fmt_complex(z: complex, digits: int = 13) -> str:
    if abs(z.imag) < 5e-15:
        return f"{z.real:.{digits}g}"
    sign = "+" if z.imag >= 0 else "-"
    return f"{z.real:.{digits}g}{sign}{abs(z.imag):.{digits}g}i"


def frac_tex(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return rf"\frac{{{q.numerator}}}{{{q.denominator}}}"


def latex_real(value: float, digits: int = 10) -> str:
    """Format a real number as compact LaTeX, including scientific notation."""

    if value == 0.0:
        return "0"
    text = f"{value:.{digits}g}"
    if "e" not in text and "E" not in text:
        return text
    mantissa, exponent = text.lower().split("e")
    exp = int(exponent)
    if mantissa in {"1", "+1"}:
        return rf"10^{{{exp}}}"
    if mantissa == "-1":
        return rf"-10^{{{exp}}}"
    return rf"{mantissa}\mathbin{{\times}}10^{{{exp}}}"


def latex_complex(value: complex, digits: int = 10) -> str:
    r"""Format a complex number with the report's ``\mathrm i`` convention."""

    z = complex(value)
    if abs(z.imag) < 5.0e-15:
        return latex_real(z.real, digits)
    if abs(z.real) < 5.0e-15:
        imag = latex_real(abs(z.imag), digits)
        sign = "-" if z.imag < 0 else ""
        return rf"{sign}{imag}\,\mathrm{{i}}"
    sign = "+" if z.imag >= 0 else "-"
    return rf"{latex_real(z.real, digits)}{sign}{latex_real(abs(z.imag), digits)}\,\mathrm{{i}}"


def write_outputs(
    out: Path,
    grid: FabiusGrid,
    diff: DifferenceGrid,
    checks_quantile: list[Check],
    checks_negative: list[Check],
    checks_log: list[Check],
    checks_caputo: list[Check],
    endpoint_rows: list[tuple[float, float]],
    stieltjes_rows: list[tuple[complex, complex, float, float]],
    series_rows: list[tuple[complex, complex, int, float]],
    jump_rows: list[tuple[float, float]],
    weyl_rows: list[tuple[float, float, float, float]],
    refinement_rows: list[tuple[float, float, float, float]],
    energy_rows: list[tuple[float, float, float]],
    exact_even: list[tuple[int, Fraction, float]],
    centered: list[Fraction],
    moments: list[Fraction],
) -> None:
    """Write a plain transcript and a compact LaTeX fragment."""

    txt: list[str] = []
    txt.append("Fabius/Rvachev fractional-integral numerical experiments")
    txt.append("=" * 66)
    txt.append(f"up mass             = {np.trapezoid(grid.up, grid.y):.17g}")
    txt.append(f"up maximum          = {np.max(grid.up):.17g}")
    txt.append(f"centered variance   = {np.trapezoid(grid.y**2 * grid.up, grid.y):.17g} (exact 1/9)")
    txt.append(f"F(1/4)              = {float(grid.F_interp(0.25)):.17g} (exact 5/72)")
    txt.append(f"difference mass     = {np.trapezoid(diff.h, diff.a):.17g}")
    txt.append(f"difference variance = {np.trapezoid(diff.a**2 * diff.h, diff.a):.17g} (exact 1/18)")
    txt.append("")

    def append_checks(title: str, rows: Iterable[Check]) -> None:
        txt.append(title)
        txt.append("-" * len(title))
        for row in rows:
            txt.append(
                f"{row.name:34s} lhs={fmt_complex(row.lhs):>26s} "
                f"rhs={fmt_complex(row.rhs):>26s} rel={row.rel_error:.3e}"
            )
        txt.append("")

    append_checks("Quantile transmutation", checks_quantile)
    append_checks("Entire continuation to negative powers", checks_negative)
    append_checks("Logarithmic derivatives at p=0", checks_log)
    append_checks("Caputo transmutation", checks_caputo)

    txt.append("Endpoint normalized ratio")
    txt.append("-------------------------")
    for u, ratio in endpoint_rows:
        txt.append(f"u={u:.1e} ratio={ratio:.12f}")
    txt.append("")

    txt.append("Generalized Stieltjes functional equations")
    txt.append("-------------------------------------------")
    for z, lam, r1, r2 in stieltjes_rows:
        txt.append(f"z={z!s:18s} lambda={lam!s:14s} differential={r1:.3e} order-recurrence={r2:.3e}")
    txt.append("")

    txt.append("Moment-series convergence")
    txt.append("-------------------------")
    for z, lam, n, err in series_rows:
        txt.append(f"z={z!s:18s} lambda={lam!s:14s} terms={n:2d} abs_error={err:.3e}")
    txt.append("")

    txt.append("Boundary jump")
    txt.append("-------------")
    for eps, err in jump_rows:
        txt.append(f"epsilon={eps:.1e} abs_error={err:.3e}")
    txt.append("")

    txt.append("Weyl tail expansion")
    txt.append("-------------------")
    for x, alpha, direct, series in weyl_rows:
        txt.append(f"x={x:.2f} alpha={alpha:.2f} direct={direct:.15g} series={series:.15g} rel={abs(direct-series)/abs(direct):.3e}")
    txt.append("")

    txt.append("Difference refinement")
    txt.append("---------------------")
    for a, beta, lhs, rhs in refinement_rows:
        txt.append(f"a={a:+.2f} beta={beta:.2f} lhs={lhs:.15g} rhs={rhs:.15g} rel={abs(lhs-rhs)/abs(lhs):.3e}")
    txt.append("")

    txt.append("Fractional energy")
    txt.append("-----------------")
    for beta, direct, fourier in energy_rows:
        txt.append(f"beta={beta:.2f} direct={direct:.15g} fourier={fourier:.15g} rel={abs(direct-fourier)/abs(direct):.3e}")
    txt.append("")

    txt.append("Exact even K_{2n}(0), Gamma-normalized")
    txt.append("--------------------------------------")
    for n, exact, numeric in exact_even:
        txt.append(f"2n={2*n:2d} exact={exact!s:>26s} numeric={numeric:.17g}")
    txt.append("")
    txt.append("First exact centered moments c_n=E[Y^(2n)]:")
    txt.append(", ".join(str(q) for q in centered[:7]))
    txt.append("First exact standard moments d_n=E[X^n]:")
    txt.append(", ".join(str(q) for q in moments[:7]))

    (out / "numerical_results.txt").write_text("\n".join(txt) + "\n", encoding="utf-8")

    # LaTeX fragment.  Keep it free of package assumptions beyond booktabs.
    tex: list[str] = []
    tex.append(r"% Automatically generated by numerical_experiments.py")
    tex.append(r"\begin{table}[htbp]")
    tex.append(r"\centering\small")
    tex.append(r"\caption{Independent checks of the quantile--Volterra and Caputo transmutations.}")
    tex.append(r"\label{tab:quantile-checks}")
    tex.append(r"\begin{tabular}{@{}lrrr@{}}")
    tex.append(r"\toprule")
    tex.append(r"case & direct form & transmuted form & relative error\\")
    tex.append(r"\midrule")
    for row in checks_quantile + checks_negative + checks_log + checks_caputo:
        lhs = latex_complex(row.lhs, 10)
        rhs = latex_complex(row.rhs, 10)
        rel = latex_real(row.rel_error, 3)
        tex.append(f"{row.name} & ${lhs}$ & ${rhs}$ & ${rel}$\\\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    tex.append("")

    tex.append(r"\begin{table}[htbp]")
    tex.append(r"\centering\small")
    tex.append(r"\caption{Generalized Stieltjes equations and moment-series convergence.}")
    tex.append(r"\label{tab:stieltjes-checks}")
    tex.append(r"\begin{tabular}{@{}lllrr@{}}")
    tex.append(r"\toprule")
    tex.append(r"$z$ & $\lambda$ & test & truncation & absolute residual\\")
    tex.append(r"\midrule")
    for z, lam, r1, r2 in stieltjes_rows:
        z_tex = latex_complex(z, 6)
        lam_tex = latex_complex(lam, 6)
        tex.append(f"${z_tex}$ & ${lam_tex}$ & differential--dyadic & -- & ${latex_real(r1, 3)}$\\\\")
        tex.append(f"${z_tex}$ & ${lam_tex}$ & order recurrence & -- & ${latex_real(r2, 3)}$\\\\")
    for z, lam, n, err in series_rows:
        z_tex = latex_complex(z, 6)
        lam_tex = latex_complex(lam, 6)
        tex.append(f"${z_tex}$ & ${lam_tex}$ & moment series & {n} & ${latex_real(err, 3)}$\\\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    tex.append("")

    tex.append(r"\begin{table}[htbp]")
    tex.append(r"\centering\small")
    tex.append(r"\caption{Nonlocal tails and the entire-order difference hierarchy.}")
    tex.append(r"\label{tab:nonlocal-checks}")
    tex.append(r"\begin{tabular}{@{}lrrrr@{}}")
    tex.append(r"\toprule")
    tex.append(r"test & parameters & direct & predicted & relative error\\")
    tex.append(r"\midrule")
    for x, alpha, direct, series in weyl_rows:
        rel = abs(direct - series) / abs(direct)
        tex.append(fr"Weyl tail & $x={x},\ \alpha={alpha}$ & ${latex_real(direct, 10)}$ & ${latex_real(series, 10)}$ & ${latex_real(rel, 3)}$\\")
    for a, beta, lhs, rhs in refinement_rows:
        rel = abs(lhs - rhs) / abs(lhs)
        tex.append(fr"$K_\beta$ refinement & $a={a},\ \beta={beta}$ & ${latex_real(lhs, 10)}$ & ${latex_real(rhs, 10)}$ & ${latex_real(rel, 3)}$\\")
    for beta, direct, fourier in energy_rows:
        rel = abs(direct - fourier) / abs(direct)
        tex.append(fr"fractional energy & $\beta={beta}$ & ${latex_real(direct, 10)}$ & ${latex_real(fourier, 10)}$ & ${latex_real(rel, 3)}$\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    tex.append("")

    tex.append(r"\begin{table}[htbp]")
    tex.append(r"\centering\small")
    tex.append(r"\caption{Exact Gamma-normalized even values of the difference hierarchy.}")
    tex.append(r"\label{tab:exact-even-K}")
    tex.append(r"\begingroup")
    tex.append(r"\renewcommand{\arraystretch}{1.70}")
    tex.append(r"\begin{tabular}{@{}ccc@{}}")
    tex.append(r"\toprule")
    tex.append(r"order & exact $K_{2n}(0)$ & numerical value\\")
    tex.append(r"\midrule")
    for n, exact, numeric in exact_even:
        tex.append(f"${2*n}$ & $\\displaystyle {frac_tex(exact)}$ & ${latex_real(numeric, 12)}$\\\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\endgroup")
    tex.append(r"\end{table}")
    tex.append("")

    tex.append(r"\begin{table}[htbp]")
    tex.append(r"\centering\small")
    tex.append(r"\caption{Approach to the leading slowly-varying fractional-integral asymptotic for $\beta=0.7$, $p=1$.}")
    tex.append(r"\label{tab:endpoint-ratio}")
    tex.append(r"\begin{tabular}{@{}cc@{}}")
    tex.append(r"\toprule")
    tex.append(r"$u$ & $\Gamma(\beta+1)I^\beta G(u)/(u^\beta G(u))$\\")
    tex.append(r"\midrule")
    for u, ratio in endpoint_rows:
        tex.append(f"${latex_real(u, 1)}$ & ${ratio:.10f}$\\\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")

    (out / "numerical_results.tex").write_text("\n".join(tex) + "\n", encoding="utf-8")


def run(out: Path, N: int) -> None:
    out.mkdir(parents=True, exist_ok=True)
    grid = reconstruct_fabius_grid(N=N)
    diff = difference_grid(grid)
    moments = standard_moments(60)
    centered = centered_moments(30)

    checks_quantile: list[Check] = []
    for u, beta, p in [(0.2, 0.6, 1.0), (0.5, 1.4, 2.3), (0.8, 0.75, 0.4)]:
        lhs = rl_quantile_direct(grid, u, beta, p)
        rhs = rl_quantile_transmuted(grid, u, beta, p)
        checks_quantile.append(Check(fr"$u={u},\beta={beta},p={p}$", lhs, rhs))

    checks_negative: list[Check] = []
    for u, beta, p in [(0.5, 0.8, -0.7), (0.8, 1.3, -1.2), (0.2, 0.6, -0.4)]:
        lhs = rl_quantile_direct(grid, u, beta, p)
        rhs = rl_quantile_regularized(grid, u, beta, p)
        checks_negative.append(Check(fr"$u={u},\beta={beta},p={p}$", lhs, rhs))

    checks_log: list[Check] = []
    for m in [1, 2, 3]:
        lhs = rl_log_direct(grid, 0.6, 0.7, m)
        rhs = rl_log_transmuted(grid, 0.6, 0.7, m)
        checks_log.append(Check(fr"$u=0.6,\beta=0.7,m={m}$", lhs, rhs))

    checks_caputo: list[Check] = []
    for u, alpha, p in [(0.2, 0.3, 1.0), (0.5, 0.7, 1.0), (0.8, 0.45, 1.0)]:
        lhs = caputo_direct(grid, u, alpha, p)
        rhs = caputo_transmuted(grid, u, alpha, p)
        checks_caputo.append(Check(fr"$u={u},\alpha={alpha},p={p}$", lhs, rhs))

    endpoint_rows = [(u, endpoint_ratio(grid, u, 0.7, 1.0)) for u in [1e-2, 1e-4, 1e-6]]

    stieltjes_rows: list[tuple[complex, complex, float, float]] = []
    for z, lam in [(1.7 + 0.4j, 0.6 + 0.3j), (2.2 + 0j, 1.4 + 0j), (-0.7 + 0.5j, 0.8 + 0j)]:
        lhs_d = generalized_stieltjes_derivative_density(grid, z, lam)
        rhs_d = (2.0 ** (lam + 1.0)) * (
            generalized_stieltjes_density(grid, 2.0 * z, lam)
            - generalized_stieltjes_density(grid, 2.0 * z - 1.0, lam)
        )
        lhs_o = generalized_stieltjes_density(grid, z, lam)
        rhs_o = (2.0**lam) / (1.0 - lam) * (
            generalized_stieltjes_density(grid, 2.0 * z, lam - 1.0)
            - generalized_stieltjes_density(grid, 2.0 * z - 1.0, lam - 1.0)
        )
        stieltjes_rows.append((z, lam, abs(lhs_d - rhs_d), abs(lhs_o - rhs_o)))

    series_rows: list[tuple[complex, complex, int, float]] = []
    for z, lam in [(2.2 + 0j, 1.4 + 0j), (1.7 + 0.4j, 0.6 + 0.3j)]:
        exact = generalized_stieltjes_density(grid, z, lam)
        for n in [5, 10, 20, 30]:
            approx = generalized_stieltjes_moment_series(z, lam, moments, n)
            series_rows.append((z, lam, n, abs(approx - exact)))

    x0, lam_jump = 0.4, 0.35
    predicted_jump = boundary_jump_reference(grid, x0, lam_jump)
    jump_rows: list[tuple[float, float]] = []
    for eps in [1e-2, 3e-3, 1e-3, 3e-4, 1e-4]:
        observed = generalized_stieltjes_density(grid, x0 + 1j * eps, lam_jump) - generalized_stieltjes_density(grid, x0 - 1j * eps, lam_jump)
        jump_rows.append((eps, abs(observed - predicted_jump)))

    weyl_rows: list[tuple[float, float, float, float]] = []
    for x, alpha, terms in [(1.2, 0.4, 18), (1.5, 0.8, 18), (2.0, 0.6, 12)]:
        direct = weyl_left_tail_direct(grid, x, alpha)
        series = weyl_left_tail_series(x, alpha, centered, terms)
        weyl_rows.append((x, alpha, direct, series))

    refinement_rows: list[tuple[float, float, float, float]] = []
    for a0, beta in [(-0.2, 0.4), (0.0, 0.8), (0.25, 1.3), (0.5, 0.6)]:
        lhs = K_beta_quad(diff, a0, beta)
        rhs = K_beta_refined(diff, a0, beta)
        refinement_rows.append((a0, beta, lhs, rhs))

    energy_rows: list[tuple[float, float, float]] = []
    for beta in [0.4, 0.8, 1.0, 1.5]:
        direct = K_beta_quad(diff, 0.0, beta)
        fourier = fractional_energy_fourier(grid, centered, beta)
        energy_rows.append((beta, direct, fourier))

    exact_even: list[tuple[int, Fraction, float]] = []
    for n in range(1, 6):
        exact = K_even_exact(n, centered)
        numeric = K_beta_quad(diff, 0.0, 2 * n)
        exact_even.append((n, exact, numeric))

    write_outputs(
        out,
        grid,
        diff,
        checks_quantile,
        checks_negative,
        checks_log,
        checks_caputo,
        endpoint_rows,
        stieltjes_rows,
        series_rows,
        jump_rows,
        weyl_rows,
        refinement_rows,
        energy_rows,
        exact_even,
        centered,
        moments,
    )
    make_figures(out, grid, diff, moments, centered)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="use N=2^15 instead of 2^17 for a faster smoke test",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for tables and figures (default: script directory)",
    )
    args = parser.parse_args()
    run(args.output, N=2**15 if args.quick else 2**17)
