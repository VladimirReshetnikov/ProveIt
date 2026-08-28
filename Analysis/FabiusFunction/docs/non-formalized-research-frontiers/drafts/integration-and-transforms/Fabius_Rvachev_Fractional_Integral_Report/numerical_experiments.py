#!/usr/bin/env python3
"""Numerical checks for the Fabius--Rvachev fractional-calculus report.

The script reconstructs Rvachev's up-function by Fourier inversion of its
infinite sinc product, obtains the Fabius CDF and quantile by monotone
interpolation, and then checks formulas that are mathematically independent of
that reconstruction:

* the complex-order generalized Stieltjes hierarchy;
* the exact exterior moment expansion of the Riesz fractional Laplacian;
* the Caputo derivative transmutation for powers of the inverse Fabius function;
* the standard-fractional bridge from F to up;
* the complex-order inverse-resolvent transmutation;
* the endpoint asymptotic of the Caputo derivative of Q^r;
* the zero pattern of the Riesz fractional Laplacian of up via a
  nonperiodic singular-integral quadrature.

No random sampling is used.  Exact centered moments are generated from the
rational moment recurrence and are therefore independent of the FFT inversion.
The script writes JSON, a small LaTeX table, and two diagnostic plots.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import cumulative_trapezoid, quad
from scipy.interpolate import PchipInterpolator
from scipy.special import gamma, poch, roots_jacobi


ROOT = Path(__file__).resolve().parent


@dataclass(frozen=True)
class FabiusNumerics:
    """Interpolants for up, F, and Q built from the sinc product."""

    x_up: np.ndarray
    up_values: np.ndarray
    up: Callable[[np.ndarray | float], np.ndarray]
    F: Callable[[np.ndarray | float], np.ndarray]
    Q: Callable[[np.ndarray | float], np.ndarray]


def build_fabius_numerics(
    *, grid_power: int = 18, period: float = 8.0, product_terms: int = 48
) -> FabiusNumerics:
    """Reconstruct up by FFT inversion and derive F and Q.

    With the angular-frequency convention

        phi(xi) = integral up(x) exp(-i xi x) dx,

    the characteristic function is

        phi(xi) = product_{j>=1} sinc(xi / 2^j).

    A period of 8 separates the compactly supported copies of up by a wide
    zero gap.  The finite product error is O(xi^2 4^{-product_terms}) on every
    fixed frequency window.
    """

    count = 1 << grid_power
    dx = period / count
    frequencies = 2.0 * math.pi * np.fft.fftfreq(count, d=dx)

    phi = np.ones(count, dtype=np.float64)
    for j in range(1, product_terms + 1):
        # np.sinc(u) means sin(pi*u)/(pi*u).
        phi *= np.sinc((frequencies / (2.0**j)) / math.pi)

    up_periodic = np.fft.fftshift(np.fft.ifft(phi)).real / dx
    x_periodic = (np.arange(count) - count // 2) * dx

    support = (x_periodic >= -1.0) & (x_periodic <= 1.0)
    x_up = x_periodic[support]
    up_values = up_periodic[support].copy()
    # Remove roundoff-scale negative ringing while preserving normalization.
    up_values[np.abs(up_values) < 5e-15] = 0.0
    up_values = np.maximum(up_values, 0.0)
    up_values /= np.trapezoid(up_values, x_up)

    up_interp = PchipInterpolator(x_up, up_values, extrapolate=False)

    cdf_z = np.concatenate(
        ([0.0], cumulative_trapezoid(up_values, x_up))
    )
    cdf_z /= cdf_z[-1]
    cdf_z = np.maximum.accumulate(np.clip(cdf_z, 0.0, 1.0))
    cdf_interp = PchipInterpolator(x_up, cdf_z, extrapolate=False)

    def up_function(x: np.ndarray | float) -> np.ndarray:
        values = np.asarray(x, dtype=float)
        inside = np.abs(values) <= 1.0
        result = np.zeros_like(values, dtype=float)
        if np.any(inside):
            result[inside] = np.maximum(up_interp(values[inside]), 0.0)
        return result

    def fabius_function(x: np.ndarray | float) -> np.ndarray:
        values = np.asarray(x, dtype=float)
        result = np.empty_like(values, dtype=float)
        result[values <= 0.0] = 0.0
        result[values >= 1.0] = 1.0
        interior = (values > 0.0) & (values < 1.0)
        if np.any(interior):
            result[interior] = cdf_interp(2.0 * values[interior] - 1.0)
        return result

    # F-values on the physical x-grid are exactly the centered CDF values.
    physical_x = (x_up + 1.0) / 2.0
    F_values = np.maximum.accumulate(cdf_z)
    unique_F, first_indices = np.unique(F_values, return_index=True)
    unique_x = physical_x[first_indices]

    # Enforce exact endpoint pairs before constructing the inverse interpolant.
    if unique_F[0] > 0.0:
        unique_F = np.concatenate(([0.0], unique_F))
        unique_x = np.concatenate(([0.0], unique_x))
    else:
        unique_x[0] = 0.0
    if unique_F[-1] < 1.0:
        unique_F = np.concatenate((unique_F, [1.0]))
        unique_x = np.concatenate((unique_x, [1.0]))
    else:
        unique_x[-1] = 1.0

    quantile_interp = PchipInterpolator(unique_F, unique_x, extrapolate=False)

    def quantile_function(y: np.ndarray | float) -> np.ndarray:
        values = np.asarray(y, dtype=float)
        result = np.empty_like(values, dtype=float)
        result[values <= 0.0] = 0.0
        result[values >= 1.0] = 1.0
        interior = (values > 0.0) & (values < 1.0)
        if np.any(interior):
            result[interior] = quantile_interp(values[interior])
        return result

    return FabiusNumerics(
        x_up=x_up,
        up_values=up_values,
        up=up_function,
        F=fabius_function,
        Q=quantile_function,
    )


def exact_centered_moments(max_index: int) -> list[float]:
    """Return c_k = E[Z^(2k)] exactly (then converted to float).

    The one-sided moments m_n = E[Y^n] satisfy

        (2^n - 1) m_n = sum_{j<n} binom(n,j) m_j/(n-j+1).

    The centered even moments obey c_k = 2 m_{2k+1}/(2k+1).
    """

    max_n = 2 * max_index + 1
    moments: list[Fraction] = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        numerator = sum(
            Fraction(math.comb(n, j), n - j + 1) * moments[j]
            for j in range(n)
        )
        moments.append(numerator / (2**n - 1))

    return [float(Fraction(2, 2 * k + 1) * moments[2 * k + 1]) for k in range(max_index + 1)]


def generalized_stieltjes_direct(
    model: FabiusNumerics, lam: float, z: float
) -> float:
    return float(
        np.trapezoid(
            model.up_values * (z - model.x_up) ** (-lam), model.x_up
        )
    )


def generalized_stieltjes_series(
    centered_moments: list[float], lam: float, z: float, terms: int
) -> float:
    total = 0.0
    for k in range(terms):
        total += (
            poch(lam, 2 * k)
            * centered_moments[k]
            / (math.factorial(2 * k) * z ** (2 * k))
        )
    return float(z ** (-lam) * total)


def fractional_laplacian_constant(beta: float) -> float:
    """The one-dimensional singular-integral normalization C_{1,beta}."""

    return float(
        beta
        * 2.0 ** (beta - 1.0)
        * gamma((1.0 + beta) / 2.0)
        / (math.sqrt(math.pi) * gamma(1.0 - beta / 2.0))
    )



def fractional_laplacian_evaluator(
    model: FabiusNumerics, beta: float, *, quadrature_order: int = 160
) -> Callable[[float], float]:
    """Build a nonperiodic evaluator for (-Delta)^(beta/2) up.

    Inside (-1,1), the principal-value integral is split symmetrically about
    x.  For x >= 0, with A=1+x and B=1-x,

      PV int_{-1}^1 [f(x)-f(t)]/|x-t|^(1+beta) dt

    equals

      int_0^B [2f(x)-f(x-u)-f(x+u)]/u^(1+beta) du
      + int_B^A [f(x)-f(x-u)]/u^(1+beta) du.

    The first numerator is O(u^2), so Gauss--Jacobi quadrature with weight
    u^(1-beta) removes the apparent singularity for every 0 < beta < 2.
    The compact-support tails are then added in closed form.  Outside the
    support, ordinary Gauss--Legendre quadrature evaluates the exact Stieltjes
    integral.  Evenness supplies negative x.

    This route avoids the algebraic periodic-image error that would arise by
    applying |xi|^beta on a finite periodic FFT box.
    """

    if not 0.0 < beta < 2.0:
        raise ValueError("beta must lie in (0,2)")

    # Weight (1+x)^(1-beta) on [-1,1], corresponding after t=(1+x)/2
    # to t^(1-beta) on [0,1].
    jacobi_nodes, jacobi_weights = roots_jacobi(
        quadrature_order, 0.0, 1.0 - beta
    )
    jacobi_t = (jacobi_nodes + 1.0) / 2.0
    jacobi_scale = 2.0 ** (-(2.0 - beta))

    legendre_nodes, legendre_weights = np.polynomial.legendre.leggauss(
        quadrature_order
    )

    # A somewhat denser fixed rule handles the nonsingular exterior integral,
    # including its finite boundary value at |x|=1 (up is flat there).
    exterior_nodes, exterior_weights = np.polynomial.legendre.leggauss(
        max(2 * quadrature_order, 256)
    )
    exterior_up = np.asarray(model.up(exterior_nodes), dtype=float)
    normalization = fractional_laplacian_constant(beta)

    def evaluate(x: float) -> float:
        x = abs(float(x))

        if x >= 1.0:
            integral = float(
                np.dot(
                    exterior_weights,
                    exterior_up / (x - exterior_nodes) ** (1.0 + beta),
                )
            )
            return -normalization * integral

        fx = float(model.up(x))
        left_radius = 1.0 + x
        right_radius = 1.0 - x

        # Symmetric local part.  Dividing the second difference by u^2 leaves
        # a bounded function, while the Jacobi rule integrates u^(1-beta).
        u = right_radius * jacobi_t
        second_difference = (
            2.0 * fx - model.up(x - u) - model.up(x + u)
        )
        symmetric_part = (
            right_radius ** (2.0 - beta)
            * jacobi_scale
            * float(np.dot(jacobi_weights, second_difference / (u * u)))
        )

        # The unmatched interval has u in [1-x,1+x], hence no singularity.
        if x == 0.0:
            unmatched_part = 0.0
        else:
            unmatched_u = 1.0 + x * legendre_nodes
            unmatched_part = x * float(
                np.dot(
                    legendre_weights,
                    (fx - model.up(x - unmatched_u))
                    / unmatched_u ** (1.0 + beta),
                )
            )

        # Contributions from (-infinity,-1) and (1,infinity), where up=0.
        support_tail = fx / beta * (
            left_radius ** (-beta) + right_radius ** (-beta)
        )
        return normalization * (
            symmetric_part + unmatched_part + support_tail
        )

    return evaluate


def fractional_laplacian_profiles(
    model: FabiusNumerics,
    betas: list[float],
    *,
    quadrature_order: int = 160,
    profile_points: int = 601,
) -> tuple[np.ndarray, dict[float, np.ndarray], dict[float, float], dict[float, int]]:
    """Evaluate nonperiodic profiles and locate their positive zero.

    The common grid contains x=0, x=1, and extends to x=1.5.  A sign-change
    count on [0,1] is recorded before Brent refinement of the unique observed
    root.  This remains numerical evidence, not a proof of the one-node law.
    """

    from scipy.optimize import brentq

    x = np.linspace(0.0, 1.5, profile_points)
    inside_count = int(round((1.0 / 1.5) * (profile_points - 1))) + 1
    if not math.isclose(x[inside_count - 1], 1.0, rel_tol=0.0, abs_tol=1e-14):
        raise ValueError("profile grid must contain x=1 exactly")

    profiles: dict[float, np.ndarray] = {}
    roots: dict[float, float] = {}
    sign_change_counts: dict[float, int] = {}

    for beta in betas:
        evaluator = fractional_laplacian_evaluator(
            model, beta, quadrature_order=quadrature_order
        )
        values = np.array([evaluator(float(point)) for point in x])
        profiles[beta] = values

        inside_values = values[:inside_count]
        changes = np.flatnonzero(
            np.signbit(inside_values[:-1]) != np.signbit(inside_values[1:])
        )
        sign_change_counts[beta] = int(len(changes))
        if len(changes) != 1:
            raise RuntimeError(
                f"expected one resolved positive sign change for beta={beta}, "
                f"found {len(changes)}"
            )
        i = int(changes[0])
        roots[beta] = float(
            brentq(
                evaluator,
                float(x[i]),
                float(x[i + 1]),
                xtol=2e-13,
                rtol=2e-13,
            )
        )

    return x, profiles, roots, sign_change_counts

def caputo_l1(
    function: Callable[[np.ndarray], np.ndarray], endpoint: float, beta: float, steps: int
) -> float:
    """L1 approximation of the left Caputo derivative, 0 < beta < 1."""

    h = endpoint / steps
    grid = np.linspace(0.0, endpoint, steps + 1)
    values = np.asarray(function(grid), dtype=float)
    increments = values[1:] - values[:-1]
    indices = np.arange(steps, dtype=float)
    weights = (indices + 1.0) ** (1.0 - beta) - indices ** (1.0 - beta)
    return float(
        h ** (-beta)
        * np.dot(weights, increments[::-1])
        / gamma(2.0 - beta)
    )


def caputo_inverse_power_transmutation(
    model: FabiusNumerics, y: float, beta: float, power: float
) -> float:
    """Evaluate the exact F-side formula for D_C^beta Q(y)^power.

    The algebraic quadrature weight factors out both endpoint singularities:

      integral_0^1 t^(power-1) (1-t)^(-beta) g(t) dt.
    """

    q = float(model.Q(y))
    fprime_q = 2.0 * float(model.up(2.0 * q - 1.0))
    # Convexity and F(0)=0 imply q F'(q)/F(q) >= 1.
    endpoint_ratio = max(q * fprime_q / y, 1.0)

    def regular_factor(t: float) -> float:
        if t <= 0.0:
            return 1.0
        if t >= 1.0:
            return endpoint_ratio ** (-beta)
        ratio = (1.0 - float(model.F(q * t)) / y) / (1.0 - t)
        # The exact ratio is at least one by convexity: F(qt) <= tF(q).
        # Enforcing that inequality removes interpolation noise near t=1.
        ratio = max(ratio, 1.0)
        return ratio ** (-beta)

    # Gauss--Jacobi quadrature integrates the algebraic weight exactly in the
    # measure and never samples the singular endpoints.
    jacobi_nodes, jacobi_weights = roots_jacobi(256, -beta, power - 1.0)
    t_nodes = (jacobi_nodes + 1.0) / 2.0
    regular_values = np.array([regular_factor(float(t)) for t in t_nodes])
    weighted_integral = (
        2.0 ** (-(power - beta))
        * float(np.dot(jacobi_weights, regular_values))
    )
    return float(
        power
        * q**power
        * y ** (-beta)
        * weighted_integral
        / gamma(1.0 - beta)
    )


def fractional_bridge_rhs(
    model: FabiusNumerics, x: float, beta: float
) -> float:
    """Compute 2^beta I_{-1+}^{1-beta} up(2x-1)."""

    a = 2.0 * x - 1.0
    length = a + 1.0

    def regular_factor(t: float) -> float:
        # s = -1 + length*t; the Jacobi weight supplies (1-t)^(-beta).
        s = -1.0 + length * t
        return float(model.up(s))

    weighted_integral, _ = quad(
        regular_factor,
        0.0,
        1.0,
        weight="alg",
        wvar=(0.0, -beta),
        epsabs=3e-12,
        epsrel=3e-12,
        limit=300,
    )
    return float(
        2.0**beta * length ** (1.0 - beta) * weighted_integral / gamma(1.0 - beta)
    )


def inverse_resolvent_lhs(
    model: FabiusNumerics, lam: float, z: float, power: float
) -> float:
    value, _ = quad(
        lambda y: (z - y) ** (-lam) * float(model.Q(y)) ** power,
        0.0,
        1.0,
        epsabs=2e-11,
        epsrel=2e-11,
        limit=300,
    )
    return float(value)


def inverse_resolvent_rhs(
    model: FabiusNumerics, lam: float, z: float, power: float
) -> float:
    integral, _ = quad(
        lambda x: (z - float(model.F(x))) ** (1.0 - lam)
        * power
        * x ** (power - 1.0),
        0.0,
        1.0,
        epsabs=2e-11,
        epsrel=2e-11,
        limit=300,
    )
    return float((integral - (z - 1.0) ** (1.0 - lam)) / (1.0 - lam))


def run() -> dict[str, object]:
    model = build_fabius_numerics()
    centered = exact_centered_moments(40)

    # Basic reconstruction check against the exact dyadic value F(1/4)=5/72.
    dyadic_value = float(model.F(0.25))
    dyadic_error = abs(dyadic_value - 5.0 / 72.0)

    # Complex-order generalized Stieltjes transform and its dyadic hierarchy.
    lam_s, z_s = 1.6, 1.7
    S_direct = generalized_stieltjes_direct(model, lam_s, z_s)
    S_series = generalized_stieltjes_series(centered, lam_s, z_s, 24)
    S_recurrence = (
        2.0 ** (lam_s - 1.0)
        / (1.0 - lam_s)
        * (
            generalized_stieltjes_direct(model, lam_s - 1.0, 2.0 * z_s + 1.0)
            - generalized_stieltjes_direct(model, lam_s - 1.0, 2.0 * z_s - 1.0)
        )
    )

    # Exterior Riesz fractional-Laplacian moment expansion.
    beta_r, x_r = 0.75, 1.35
    c_beta = fractional_laplacian_constant(beta_r)
    riesz_direct = -c_beta * generalized_stieltjes_direct(model, 1.0 + beta_r, x_r)
    riesz_series = -c_beta * generalized_stieltjes_series(
        centered, 1.0 + beta_r, x_r, 32
    )

    # Caputo derivative of Q and the independent L1 discretization.
    y_c, beta_c, power_c = 0.2, 0.4, 1.0
    caputo_exact = caputo_inverse_power_transmutation(
        model, y_c, beta_c, power_c
    )
    caputo_l1_value = caputo_l1(
        lambda u: model.Q(u) ** power_c, y_c, beta_c, 20000
    )

    # Standard fractional derivative bridge from F to up.
    x_b, beta_b = 0.3, 0.6
    bridge_exact = fractional_bridge_rhs(model, x_b, beta_b)
    bridge_l1 = caputo_l1(model.F, x_b, beta_b, 20000)

    # Complex-order inverse-resolvent transmutation.
    lam_t, z_t, power_t = 0.8, 1.7, 1.3
    inverse_resolvent_direct = inverse_resolvent_lhs(model, lam_t, z_t, power_t)
    inverse_resolvent_transmuted = inverse_resolvent_rhs(
        model, lam_t, z_t, power_t
    )

    # Endpoint convergence for the new Caputo asymptotic.
    endpoint_y = np.logspace(-2.0, -7.0, 11)
    endpoint_ratios: list[float] = []
    for y in endpoint_y:
        exact = caputo_inverse_power_transmutation(model, float(y), 0.4, 1.0)
        leading = float(model.Q(y)) * y ** (-0.4) / gamma(0.6)
        endpoint_ratios.append(float(exact / leading))

    # Exploratory zero locations for the Riesz fractional Laplacian.  These
    # are deliberately kept separate from the exterior theorem above: the
    # one-node statement suggested by these profiles remains conjectural.
    root_betas = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75]
    profile_x, profiles, positive_roots, root_sign_changes = (
        fractional_laplacian_profiles(model, root_betas)
    )

    results: dict[str, object] = {
        "parameters": {
            "fft_grid_power": 18,
            "fft_period": 8.0,
            "sinc_product_terms": 48,
            "caputo_l1_steps": 20000,
        },
        "dyadic_F_quarter": {
            "computed": dyadic_value,
            "exact": 5.0 / 72.0,
            "absolute_error": dyadic_error,
        },
        "generalized_stieltjes": {
            "lambda": lam_s,
            "z": z_s,
            "direct": S_direct,
            "moment_series": S_series,
            "hierarchy_rhs": S_recurrence,
            "series_absolute_error": abs(S_direct - S_series),
            "hierarchy_absolute_error": abs(S_direct - S_recurrence),
        },
        "riesz_exterior": {
            "beta": beta_r,
            "x": x_r,
            "direct": riesz_direct,
            "moment_series": riesz_series,
            "absolute_error": abs(riesz_direct - riesz_series),
        },
        "caputo_inverse_power": {
            "y": y_c,
            "beta": beta_c,
            "power": power_c,
            "transmutation": caputo_exact,
            "L1_discretization": caputo_l1_value,
            "absolute_error": abs(caputo_exact - caputo_l1_value),
        },
        "fractional_F_to_up_bridge": {
            "x": x_b,
            "beta": beta_b,
            "up_integral": bridge_exact,
            "L1_discretization": bridge_l1,
            "absolute_error": abs(bridge_exact - bridge_l1),
        },
        "inverse_resolvent": {
            "lambda": lam_t,
            "z": z_t,
            "power": power_t,
            "direct": inverse_resolvent_direct,
            "transmuted": inverse_resolvent_transmuted,
            "absolute_error": abs(
                inverse_resolvent_direct - inverse_resolvent_transmuted
            ),
        },
        "caputo_endpoint_asymptotic": {
            "beta": 0.4,
            "power": 1.0,
            "y": endpoint_y.tolist(),
            "ratio_to_leading_term": endpoint_ratios,
        },
        "riesz_fractional_laplacian_positive_zero": {
            "method": (
                "nonperiodic singular integral with symmetric "
                "Gauss--Jacobi regularization"
            ),
            "quadrature_order": 160,
            "profile_points": 601,
            "resolved_sign_changes_on_0_1": {
                str(beta): root_sign_changes[beta] for beta in root_betas
            },
            "beta_to_zero": {str(beta): positive_roots[beta] for beta in root_betas},
        },
    }

    # Machine-readable JSON and a plain-text copy for quick inspection.
    serialized_results = json.dumps(results, indent=2) + "\n"
    (ROOT / "numerical_results.json").write_text(
        serialized_results, encoding="utf-8"
    )
    (ROOT / "numerical_results.txt").write_text(
        serialized_results, encoding="utf-8"
    )

    # Compact table included by the report.
    rows = [
        (
            "Generalized Stieltjes moment series",
            S_direct,
            S_series,
            abs(S_direct - S_series),
        ),
        (
            "Generalized Stieltjes hierarchy",
            S_direct,
            S_recurrence,
            abs(S_direct - S_recurrence),
        ),
        (
            "Exterior Riesz moment series",
            riesz_direct,
            riesz_series,
            abs(riesz_direct - riesz_series),
        ),
        (
            "Caputo inverse transmutation",
            caputo_exact,
            caputo_l1_value,
            abs(caputo_exact - caputo_l1_value),
        ),
        (
            "Fractional $F$--$\\operatorname{up}$ bridge",
            bridge_exact,
            bridge_l1,
            abs(bridge_exact - bridge_l1),
        ),
        (
            "Complex inverse resolvent",
            inverse_resolvent_direct,
            inverse_resolvent_transmuted,
            abs(inverse_resolvent_direct - inverse_resolvent_transmuted),
        ),
    ]
    tex_lines = [
        "\\begin{tabular}{@{}lrrr@{}}",
        "\\toprule",
        "identity & direct side & transformed side & absolute error\\\\",
        "\\midrule",
    ]
    for name, left, right, error in rows:
        tex_lines.append(
            f"{name} & {left:.12g} & {right:.12g} & {error:.3e}\\\\"
        )
    tex_lines.extend(["\\bottomrule", "\\end{tabular}"])
    (ROOT / "numerical_results.tex").write_text(
        "\n".join(tex_lines) + "\n", encoding="utf-8"
    )

    # One standalone plot; matplotlib's default palette is deliberately used.
    fig, ax = plt.subplots(figsize=(6.4, 3.8))
    ax.semilogx(endpoint_y, endpoint_ratios, marker="o")
    ax.axhline(1.0, linewidth=1.0)
    ax.invert_xaxis()
    ax.set_xlabel(r"$y$")
    ax.set_ylabel(r"$D_{0+}^{0.4}Q(y)\,/\,[Q(y)y^{-0.4}/\Gamma(0.6)]$")
    ax.set_title("Slow convergence of the inverse-Fabius Caputo endpoint law")
    ax.grid(True, which="both", linewidth=0.4)
    fig.tight_layout()
    fig.savefig(ROOT / "caputo_endpoint_ratio.png", dpi=180)
    plt.close(fig)

    # Representative nonperiodic Riesz profiles.  The plot supports, but does
    # not prove, the one-positive-node conjecture formulated in the report.
    physical = (profile_x >= 0.0) & (profile_x <= 1.5)
    fig, ax = plt.subplots(figsize=(6.4, 3.8))
    for beta in [0.5, 1.0, 1.5]:
        ax.plot(profile_x[physical], profiles[beta][physical], label=rf"$\beta={beta:g}$")
    ax.axhline(0.0, linewidth=1.0)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$(-\Delta)^{\beta/2}\operatorname{up}(x)$")
    ax.set_title("Nonperiodic Riesz fractional-Laplacian profiles")
    ax.legend()
    ax.grid(True, linewidth=0.4)
    fig.tight_layout()
    fig.savefig(ROOT / "riesz_fractional_profiles.png", dpi=180)
    plt.close(fig)

    return results


if __name__ == "__main__":
    output = run()
    print(json.dumps(output, indent=2))
