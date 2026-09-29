#!/usr/bin/env python3
"""Reproduce numerical checks for Sharp Conditioning Laws.

These are floating-point computations, not interval-certified bounds or proofs.
The finite simplex calculation is an exactly specified FINITE PROXY, not an
exact evaluation of the infinite Fabius conditioned distribution. The separate
importance-sampling experiment directly approximates that distribution.

Usage: python verification.py [--draws 240000] [--skip-monte-carlo]
Requires Python >= 3.11, numpy, scipy, matplotlib. No network access is used.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.special import ndtr
from scipy.stats import beta, gamma
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
SEED = 20260928


def tv_profile(alpha: float) -> float:
    """TV(N(0,1-alpha), N(0,1)); TV is half the L1 distance."""
    if not 0 <= alpha <= 1:
        raise ValueError("alpha must lie in [0,1]")
    if alpha == 0:
        return 0.0
    if alpha == 1:
        return 1.0
    a = math.sqrt(-math.log1p(-alpha) / alpha)
    return float(2 * (ndtr(a) - ndtr(a * math.sqrt(1-alpha))))


def simplex_tv(n: int, k: int) -> float:
    """Exact-distribution formula evaluated in double precision.

    X is uniform on {x_i>=0, sum_{i=1}^n x_i<=n}.
    Return TV(law(X_1,...,X_k), Exp(1)^k), for 1<=k<n.
    The sum divided by n has a Beta(k,n-k+1) distribution.
    """
    if not 1 <= k < n:
        raise ValueError("Require 1 <= k < n")
    log_const = float(np.log1p(-np.arange(k, dtype=float)/n).sum())
    def log_ratio(s: float) -> float:
        return log_const + s + (n-k)*math.log1p(-s/n)
    lower = 0.0 if k == 1 else brentq(log_ratio, 0.0, float(k))
    upper = brentq(log_ratio, float(k), np.nextafter(float(n), 0.0))
    conditioned_mass = beta.cdf(upper/n, k, n-k+1)-beta.cdf(lower/n, k, n-k+1)
    product_mass = gamma.cdf(upper, k)-gamma.cdf(lower, k)
    value = float(conditioned_mass-product_mass)
    if not (-1e-10 <= value <= 1+1e-10):
        raise ArithmeticError("Numerical TV value is outside [0,1]")
    return value


def trunc_mean(a: np.ndarray) -> np.ndarray:
    """Mean of an Exp(1) variable truncated to [0,a], stably evaluated."""
    a = np.asarray(a, dtype=float)
    out = np.empty_like(a)
    small = a < 1e-3
    large = a > 50
    z = a[small]
    out[small] = z/2-z*z/12+z**4/720-z**6/30240
    out[large] = 1.0  # error <= 50/(exp(50)-1) per coordinate near cutoff
    z = a[~(small | large)]
    out[~(small | large)] = 1-z/np.expm1(z)
    return out


def importance_check(n: int, draws: int, theta: float = .37, batch: int = 4000) -> dict:
    """Self-normalized importance sampling under the exact exponential tilt.

    t=2^(n+theta); the saddle x is computed as tilted_mean/t.
    Keep coordinates through n+50: omitted scaled sum <=2^(theta-50).
    Tail truncation and floating-point errors are much smaller than MC error;
    this statement is not an interval certification.
    """
    if draws < 1000:
        raise ValueError("Use at least 1000 draws")
    rng = np.random.default_rng(SEED + n)
    j = np.arange(1, n+51, dtype=float)
    a = np.exp2(n+theta-j)
    means = trunc_mean(a)
    mu = float(means.sum())
    half = n//2
    mu_half = float(means[:half].sum())
    mass = -np.expm1(-a)
    sw = sw2 = 0.0
    names = ["slack_mean", "slack_survival_1", "bridge_midpoint_second_moment",
             "boundary_coordinate_mean", "gumbel_cdf_0"]
    sf = np.zeros(len(names))
    s2f = np.zeros(len(names))
    s2f2 = np.zeros(len(names))
    for start in range(0, draws, batch):
        size = min(batch, draws-start)
        uniforms = rng.random((size, len(a)))
        y = -np.log1p(-uniforms*mass)
        total = y.sum(axis=1)
        h = mu-total
        weight = np.exp(-np.maximum(h, 0))*(h >= 0)
        mid = (y[:, :half].sum(axis=1)-mu_half)/math.sqrt(n)
        obs = np.column_stack((h, h >= 1, mid*mid, y[:, n-1],
                               y.max(axis=1)-math.log(n) <= 0)).astype(float)
        w2 = weight*weight
        sw += float(weight.sum())
        sw2 += float(w2.sum())
        sf += (weight[:, None]*obs).sum(axis=0)
        s2f += (w2[:, None]*obs).sum(axis=0)
        s2f2 += (w2[:, None]*obs*obs).sum(axis=0)
    estimate = sf/sw
    se = np.sqrt(np.maximum(s2f2-2*estimate*s2f+estimate**2*sw2, 0))/sw
    d = sw/draws
    dse = math.sqrt(max(sw2/draws-d*d, 0)/(draws-1))
    targets = [1., math.exp(-1), .25, float(means[n-1]), math.exp(-1)]
    return {
        "n": n, "theta": theta, "draws": draws, "seed": SEED+n,
        "scaled_tail_bound": 2**(theta-50), "mu": mu,
        "x": mu*2**(-n-theta), "effective_sample_size": sw*sw/sw2,
        "D_times_sqrt_2pi_n": {"estimate": d*math.sqrt(2*math.pi*n),
                               "standard_error": dse*math.sqrt(2*math.pi*n),
                               "limiting_target": 1.0},
        "observables": {name: {"estimate": float(value), "standard_error": float(error),
                               "limiting_target": target}
                        for name, value, error, target in zip(names, estimate, se, targets)}
    }



def exact_moment_checks() -> dict[str, str]:
    """Exact polynomial integrals against exponential densities via factorials."""
    p1 = {(1,): Fraction(1), (2,): Fraction(-1, 2)}
    p2 = {(0, 0): Fraction(-1), (1, 0): Fraction(2), (0, 1): Fraction(2),
          (2, 0): Fraction(-1, 2), (1, 1): Fraction(-1), (0, 2): Fraction(-1, 2)}
    def integrate(poly: dict, extra: tuple[int, ...]) -> Fraction:
        return sum((coef*math.prod(math.factorial(i+j) for i, j in zip(powers, extra))
                    for powers, coef in poly.items()), Fraction(0))
    values = {"one_coordinate_normalization": integrate(p1, (0,)),
              "one_coordinate_mean_correction": integrate(p1, (1,)),
              "one_coordinate_second_moment_correction": integrate(p1, (2,)),
              "two_coordinate_normalization": integrate(p2, (0, 0)),
              "two_coordinate_cross_moment_correction": integrate(p2, (1, 1))}
    expected = [0, -1, -6, 0, -3]
    assert list(values.values()) == expected
    return {key: str(value) for key, value in values.items()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draws", type=int, default=240000)
    parser.add_argument("--skip-monte-carlo", action="store_true")
    args = parser.parse_args()
    (ROOT/"figures").mkdir(exist_ok=True)
    (ROOT/"data").mkdir(exist_ok=True)
    alphas = [.1, .25, .5, .75, .9, .99]
    profile_rows = []
    for alpha in alphas:
        row = {"alpha": alpha, "limit": tv_profile(alpha)}
        for n in [100, 1000, 10000]:
            row[f"simplex_n_{n}"] = simplex_tv(n, int(round(alpha*n)))
        profile_rows.append(row)
    with (ROOT/"data"/"tv_profile.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(profile_rows[0]))
        writer.writeheader()
        writer.writerows(profile_rows)
    first = [{"n": n, "n_times_TV_one_coordinate": n*simplex_tv(n, 1),
              "limit": 2*math.exp(-2)} for n in [50, 100, 500, 1000, 10000]]
    checks = {
        "TV_convention": "one half of L1; supremum over events",
        "phi_1": math.exp(-.5)/math.sqrt(2*math.pi),
        "finite_simplex_is_not_exact_infinite_Fabius": True,
        "profile": profile_rows, "first_coordinate": first,
        "exact_moment_checks": exact_moment_checks(),
        "monte_carlo": []
    }
    if not args.skip_monte_carlo:
        for n in [32, 64, 128, 256]:
            result = importance_check(n, args.draws)
            checks["monte_carlo"].append(result)
            print(f"n={n}: D*sqrt(2pi n)={result['D_times_sqrt_2pi_n']}", flush=True)
    output_name = "deterministic_checks.json" if args.skip_monte_carlo else "verification_results.json"
    with (ROOT/"data"/output_name).open("w") as stream:
        json.dump(checks, stream, indent=2)
        stream.write("\n")
    xx = np.linspace(.001, .999, 500)
    fig, ax = plt.subplots(figsize=(7.1, 4.1))
    ax.plot(xx, [tv_profile(float(x)) for x in xx], label="Universal limiting profile")
    for n, marker in [(100, "o"), (1000, "s")]:
        ax.plot(alphas, [row[f"simplex_n_{n}"] for row in profile_rows],
                linestyle="none", marker=marker, markersize=5, label=f"Finite simplex, n={n}")
    ax.set_xlabel("Observed fraction of active coordinates")
    ax.set_ylabel("Total-variation distance")
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.grid(True, alpha=.25)
    ax.legend(loc="upper left", frameon=False)
    fig.tight_layout()
    fig.savefig(ROOT/"figures"/"tv_profile.pdf")
    fig.savefig(ROOT/"figures"/"tv_profile.png", dpi=170)
    plt.close(fig)
    # A separate figure illustrates the moving geometric boundary layer.
    fig, ax = plt.subplots(figsize=(7.1, 3.8))
    uu = np.linspace(0, 1, 300)
    for theta in [0, .5, 1]:
        a = 2**theta
        ax.plot(uu, a*np.exp(-a*uu)/(-math.expm1(-a)),
                label=fr"$\theta={theta:g}$")
    ax.set_xlabel(r"Original uniform coordinate $u$")
    ax.set_ylabel("Limiting conditional density")
    ax.set_xlim(0, 1)
    ax.legend(frameon=False)
    ax.grid(True, alpha=.25)
    fig.tight_layout()
    fig.savefig(ROOT/"figures"/"boundary_phase.pdf")
    fig.savefig(ROOT/"figures"/"boundary_phase.png", dpi=170)
    plt.close(fig)
    # Conservative smoke tests on deterministic computations.
    assert all(0 < row['limit'] < 1 for row in profile_rows)
    assert max(abs(row['simplex_n_10000']-row['limit']) for row in profile_rows) < .004
    assert abs(first[-1]['n_times_TV_one_coordinate']-2*math.exp(-2)) < .0002
    print(json.dumps({"profile": profile_rows, "first_coordinate": first}, indent=2))
    print("Deterministic numerical smoke tests passed. No formal certification is asserted.")


if __name__ == "__main__":
    main()
