#!/usr/bin/env python3
"""Deterministic experiments for the geometric q-Fabius--Rvachev family.

The family is
    X_q = (1-q) * sum_{j>=0} q**j U_j,  0<q<1,
with independent U_j ~ Uniform(0,1).  At q=1/2 this is the bounded
Fabius distribution.  No Monte Carlo sampling is used.

Outputs:
  q_family_densities.pdf
  standardized_cumulants.pdf
  endpoint_bound_residuals.pdf
  phase_aware_extrapolation.pdf
  numerical_summary.csv
  experiment_output.txt

Dependencies: Python 3.10+, NumPy, Matplotlib.
"""
from __future__ import annotations

import csv
import math
from dataclasses import dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
B_EVEN = {2: 1/6, 4: -1/30, 6: 1/42, 8: -1/30, 10: 5/66, 12: -691/2730}


def check_q(q: float) -> None:
    if not 0 < q < 1:
        raise ValueError("q must lie in (0,1)")


def variance(q: float) -> float:
    check_q(q)
    return (1-q)/(12*(1+q))


def centered_cumulant(q: float, order: int) -> float:
    """kappa_{2m}=B_{2m}(1-q)^(2m)/(2m(1-q^(2m))); odd cumulants vanish."""
    check_q(q)
    if order % 2:
        return 0.0
    if order not in B_EVEN:
        raise ValueError(f"Bernoulli number B_{order} not tabulated")
    return B_EVEN[order]/order * (1-q)**order/(1-q**order)


def standardized_cumulant(q: float, order: int) -> float:
    return centered_cumulant(q, order)/variance(q)**(order/2)


def gamma4(q: float) -> float:
    return -(6/5)*(1-q*q)/(1+q*q)


def gamma6(q: float) -> float:
    return (48/7)*(1-q*q)**2/(1+q*q+q**4)


@dataclass(frozen=True)
class GridLaw:
    q: float
    x: np.ndarray
    cdf: np.ndarray
    density: np.ndarray
    iterations: int
    mass_error: float
    symmetry_error: float


def cumulative_trapezoid(y: np.ndarray, dx: float) -> np.ndarray:
    out = np.empty_like(y)
    out[0] = 0.0
    out[1:] = np.cumsum((y[:-1]+y[1:])*(0.5*dx))
    return out


def extended_antiderivative(t: np.ndarray, x: np.ndarray, area: np.ndarray) -> np.ndarray:
    clipped = np.clip(t, 0.0, 1.0)
    out = np.interp(clipped, x, area)
    above = t > 1.0
    out[above] = area[-1] + t[above] - 1.0
    out[t < 0.0] = 0.0
    return out


def extended_cdf(t: np.ndarray, x: np.ndarray, cdf: np.ndarray) -> np.ndarray:
    return np.interp(t, x, cdf, left=0.0, right=1.0)


def solve_law(q: float, points: int = 30001, tol: float = 5e-12, max_iter: int = 2000) -> GridLaw:
    """Iterate F_new(x)=q/(1-q) integral_{(x-1+q)/q}^{x/q} F_old(v)dv."""
    check_q(q)
    c = 1-q
    x = np.linspace(0.0, 1.0, points)
    dx = float(x[1]-x[0])
    cdf = x.copy()  # any continuous initial law; the affine map contracts by q
    for iteration in range(1, max_iter+1):
        area = cumulative_trapezoid(cdf, dx)
        new = q/c * (
            extended_antiderivative(x/q, x, area)
            - extended_antiderivative((x-c)/q, x, area)
        )
        new = np.clip(new, 0.0, 1.0)
        new[0], new[-1] = 0.0, 1.0
        err = float(np.max(np.abs(new-cdf)))
        cdf = new
        if err < tol:
            break
    else:
        raise RuntimeError(f"no convergence for q={q}")
    density = (extended_cdf(x/q, x, cdf)-extended_cdf((x-c)/q, x, cdf))/c
    density = np.maximum(density, 0.0)
    mass_error = abs(float(np.trapezoid(density, x))-1.0)
    symmetry_error = float(np.max(np.abs(density-density[::-1])))
    return GridLaw(q, x, cdf, density, iteration, mass_error, symmetry_error)


@dataclass(frozen=True)
class EndpointRecord:
    q: float
    x: float
    lower_log: float
    upper_log: float
    main: float
    lower_residual_over_L: float
    upper_residual_over_L: float


def endpoint_bounds(q: float, x: float) -> EndpointRecord:
    """Elementary simplex/product bounds used in the endpoint theorem."""
    check_q(q)
    c = 1-q
    a = math.log(1/q)
    L = math.log(1/x)
    # Largest n such that x <= c q^(n-1).
    n_up = max(1, math.floor((L+math.log(c))/a)+1)
    while x > c*q**(n_up-1):
        n_up -= 1
    while x <= c*q**n_up:
        n_up += 1
    upper = n_up*math.log(x)-math.lgamma(n_up+1)-n_up*math.log(c)-0.5*n_up*(n_up-1)*math.log(q)
    # q^n <= x/2; force each first coordinate contribution <= x/(2n).
    n_lo = math.ceil(math.log(2/x)/a)
    alpha_max = x/(2*n_lo*c*q**(n_lo-1))
    if alpha_max >= 1:
        raise RuntimeError("x is not in the lower-bound asymptotic range")
    lower = n_lo*math.log(x)-n_lo*math.log(2*n_lo*c)-0.5*n_lo*(n_lo-1)*math.log(q)
    main = -L*L/(2*a)-L*math.log(L)/a
    return EndpointRecord(q, x, lower, upper, main, (lower-main)/L, (upper-main)/L)


def lagrange_weights_at_zero(lambdas: np.ndarray) -> np.ndarray:
    t = 1/np.asarray(lambdas, dtype=float)
    w = np.ones(len(t))
    for m in range(len(t)):
        for ell in range(len(t)):
            if ell != m:
                w[m] *= -t[ell]/(t[m]-t[ell])
    return w


def asymptotic_model(lam: np.ndarray | float) -> np.ndarray:
    """Known limit plus inverse powers with 1-periodic coefficient functions."""
    z = np.asarray(lam, dtype=float)
    u = z-np.floor(z)
    limit = 1.23456789
    a1 = 0.70+0.20*np.sin(2*np.pi*u)
    a2 = -0.35+0.15*np.cos(2*np.pi*u)
    a3 = 0.12+0.08*np.sin(4*np.pi*u)
    a4 = -0.09+0.03*np.cos(6*np.pi*u)
    a5 = 0.05+0.02*np.sin(2*np.pi*u)
    return limit+a1/z+a2/z**2+a3/z**3+a4/z**4+a5/z**5


def phase_errors() -> tuple[np.ndarray, np.ndarray, np.ndarray, float, float]:
    bases = np.arange(8.37, 80.38, 2.0)
    raw, accel = [], []
    limit = 1.23456789
    for base in bases:
        nodes = base+np.arange(4)  # integer spacing preserves fractional Lambert phase
        w = lagrange_weights_at_zero(nodes)
        raw.append(abs(float(asymptotic_model(base))-limit))
        accel.append(abs(float(w@asymptotic_model(nodes))-limit))
    raw = np.array(raw)
    accel = np.array(accel)
    tail = slice(len(bases)//2, None)
    raw_slope = float(np.polyfit(np.log(bases[tail]), np.log(raw[tail]), 1)[0])
    accel_slope = float(np.polyfit(np.log(bases[tail]), np.log(accel[tail]), 1)[0])
    return bases, raw, accel, raw_slope, accel_slope


def b_valuation(n: int, b: int) -> int:
    r = 0
    n = abs(n)
    while n % b == 0:
        n //= b
        r += 1
    return r


def direct_multiplicity(n: int, b: int) -> int:
    count, power = 0, 1
    while power <= abs(n):
        if n % power == 0:
            count += 1
        power *= b
    return count


def make_figures(laws: list[GridLaw], endpoint: list[EndpointRecord]) -> tuple[float, float]:
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    for law in laws:
        ax.plot(law.x, law.density, label=fr"$q={law.q:g}$")
    ax.set(xlabel=r"$x$", ylabel=r"$f_q(x)$", title="Densities in the geometric Fabius--Rvachev family")
    ax.legend(); ax.grid(True, alpha=0.25); fig.tight_layout()
    fig.savefig(HERE/"q_family_densities.pdf"); plt.close(fig)

    qs = np.linspace(0.05, 0.995, 600)
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    ax.plot(qs, [gamma4(float(q)) for q in qs], label=r"$\gamma_4(q)$")
    ax.plot(qs, [gamma6(float(q)) for q in qs], label=r"$\gamma_6(q)$")
    ax.axhline(0, linewidth=0.8)
    ax.set(xlabel=r"$q$", ylabel="standardized cumulant", title=r"Vanishing non-Gaussian cumulants as $q\uparrow1$")
    ax.legend(); ax.grid(True, alpha=0.25); fig.tight_layout()
    fig.savefig(HERE/"standardized_cumulants.pdf"); plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    xs = np.array([r.x for r in endpoint])
    ax.semilogx(xs, [r.lower_residual_over_L for r in endpoint], marker="o", label="lower bound")
    ax.semilogx(xs, [r.upper_residual_over_L for r in endpoint], marker="s", label="upper bound")
    ax.invert_xaxis()
    ax.set(xlabel=r"$x$", ylabel=r"$(\log\mathrm{bound}-M_q(x))/\log(1/x)$", title="Endpoint bounds after removing the first two terms")
    ax.legend(); ax.grid(True, alpha=0.25); fig.tight_layout()
    fig.savefig(HERE/"endpoint_bound_residuals.pdf"); plt.close(fig)

    bases, raw, accel, raw_slope, accel_slope = phase_errors()
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    ax.loglog(bases, raw, marker="o", label="unextrapolated")
    ax.loglog(bases, accel, marker="s", label="phase-aware degree 3")
    ax.set(xlabel=r"base Lambert coordinate $\lambda$", ylabel="absolute error", title="Periodic-phase-aware Lagrange/Richardson acceleration")
    ax.legend(); ax.grid(True, alpha=0.25); fig.tight_layout()
    fig.savefig(HERE/"phase_aware_extrapolation.pdf"); plt.close(fig)
    return raw_slope, accel_slope


def main() -> None:
    laws = [solve_law(q) for q in (0.30, 0.50, 0.75, 0.95)]
    endpoint = [endpoint_bounds(0.5, 10.0**(-k)) for k in range(4, 61, 4)]
    raw_slope, accel_slope = make_figures(laws, endpoint)

    with (HERE/"numerical_summary.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["type", "q", "x", "variance", "gamma4", "gamma6", "iterations", "diagnostic_1", "diagnostic_2"])
        for law in laws:
            w.writerow(["distribution", law.q, "", variance(law.q), gamma4(law.q), gamma6(law.q), law.iterations, law.mass_error, law.symmetry_error])
        for r in endpoint:
            w.writerow(["endpoint_bound", r.q, r.x, "", "", "", "", r.lower_residual_over_L, r.upper_residual_over_L])

    lines = ["GEOMETRIC FABIUS--RVACHEV NUMERICAL CHECKS", "="*56, "", "Fixed-point density diagnostics"]
    for law in laws:
        mid = len(law.x)//2
        lines.append(f"q={law.q:.2f}: iterations={law.iterations}, mass_error={law.mass_error:.3e}, symmetry_error={law.symmetry_error:.3e}, f(1/2)={law.density[mid]:.12g}")
        if law.q < 0.5:
            c = 1-law.q
            mask = (law.x >= law.q+0.01) & (law.x <= c-0.01)
            err = float(np.max(np.abs(law.density[mask]-1/c)))
            lines.append(f"  plateau target={1/c:.12g}, interior_mesh_error={err:.3e}")
    lines += ["", "Closed cumulant checks"]
    for q in (0.25, 0.50, 0.75, 0.90, 0.97):
        g4 = standardized_cumulant(q,4); g6 = standardized_cumulant(q,6)
        lines.append(f"q={q:.2f}: variance={variance(q):.12g}, gamma4={g4:.12g} (diff {g4-gamma4(q):+.2e}), gamma6={g6:.12g} (diff {g6-gamma6(q):+.2e})")
    lines += ["", "Endpoint residuals, q=1/2"]
    for r in endpoint[::3]:
        lines.append(f"x={r.x:.1e}: lower={r.lower_residual_over_L:+.8f}, upper={r.upper_residual_over_L:+.8f}")
    lines += ["", "Phase-aware extrapolation", f"raw log-log slope={raw_slope:.6f}", f"accelerated log-log slope={accel_slope:.6f}", "", "Reciprocal-integer zero multiplicities"]
    for b in (2,3,4,5):
        ok = all(direct_multiplicity(n,b)==1+b_valuation(n,b) for n in range(1,65))
        lines.append(f"b={b}: formula verified for n=1,...,64 -> {ok}")
    output = "\n".join(lines)+"\n"
    (HERE/"experiment_output.txt").write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
