#!/usr/bin/env python3
"""Reproducible diagnostics for the spectral-extremes theorem.

The synthetic Dirichlet spectrum uses the inverse of the leading counting
function. It is NOT a list of computed zeta zeros. The rejection experiment
samples an EXACT conditional law for a FINITE spectrum gamma_j=j; its
finite truncation is reported and is not treated as the infinite law.
Numerical diagnostics supplement, and do not establish, the proof.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.special import erfc, gammaincc, gammaln, lambertw

ROOT = Path(__file__).resolve().parents[1]


def leading_ordinates(j):
    j = np.asarray(j, dtype=float)
    return 2 * np.pi * j / lambertw(j / np.e).real


def leading_count(t):
    return t / (2 * np.pi) * (np.log(t / (2 * np.pi)) - 1)


def exponential_intensity_tail(u, threshold, last_ordinate):
    """Analytic upper bound on the omitted theta=1 intensity.

    Monotonicity bounds the sum after index J by the integral from J;
    dN_0(T)=log(T/(2pi)) dT/(2pi), and
    log(T/(2pi)) <= log(T0/(2pi)) + T/T0 for T>=T0.
    Floating-point evaluation of this bound is NOT interval arithmetic.
    """
    m, t0 = threshold, last_ordinate
    a = math.sqrt(m) * t0 / u
    integral0 = u * math.sqrt(math.pi) / (2 * math.sqrt(m)) * erfc(a)
    integral1 = u * u / (2 * m * t0) * math.exp(-a * a)
    return math.exp(-m) / (2 * math.pi) * (
        math.log(t0 / (2 * math.pi)) * integral0 + integral1
    )


def deterministic_experiments():
    z_grid = np.linspace(-2.5, 5.0, 76)
    y_grid = np.linspace(0, 3, 61)
    rows, curves = [], []
    for u in (100.0, 1000.0, 10000.0, 100000.0):
        # This deliberately generous cutoff makes the theta=1 truncation
        # bound negligible even at the left edge of the plotted window.
        truncation_height = (40 if u == 100 else 5) * u
        last = max(200, math.ceil(leading_count(truncation_height)))
        gamma = leading_ordinates(np.arange(1, last + 1))
        rates = 1 + (gamma / u) ** 2
        for theta in (0.5, 1.0, 2.0):
            intensity = lambda b: float(np.sum(gammaincc(theta, rates * b)))
            b = brentq(lambda w: intensity(w) - 1, 1e-5, 100.0,
                       xtol=2e-13)
            b_explicit = (math.log(u) + (theta - 0.5) * math.log(math.log(u))
                          - math.log(4 * math.sqrt(math.pi)) - gammaln(theta))
            cdf = []
            poisson = []
            for z in z_grid:
                if b + z <= 0:
                    cdf.append(0.0)
                    poisson.append(0.0)
                    continue
                tails = gammaincc(theta, rates * (b + z))
                cdf.append(float(np.exp(np.log1p(-tails).sum())))
                poisson.append(float(np.exp(-tails.sum())))
            tails0 = gammaincc(theta, rates * b)
            mark = [float(tails0[gamma * math.sqrt(b) / u <= y].sum())
                    for y in y_grid]
            gumbel = np.exp(-np.exp(-z_grid))
            smallest_threshold = min(b + z for z in z_grid if b + z > 0)
            tail_bound = (exponential_intensity_tail(u, smallest_threshold, gamma[-1])
                          if theta == 1 else None)
            rows.append({
                'spectrum': 'inverse leading Riemann-von Mangoldt count, synthetic',
                'u': u, 'theta': theta, 'coordinates': last,
                'b_numerical': b, 'b_explicit': b_explicit,
                'centering_difference': b - b_explicit,
                'centering_residual': intensity(b) - 1,
                'grid_cdf_error_vs_gumbel': float(np.max(np.abs(np.array(cdf) - gumbel))),
                'grid_error_independent_vs_poisson': float(np.max(np.abs(np.array(cdf) - poisson))),
                'theta1_omitted_intensity_upper_bound': tail_bound,
                'bound_threshold': smallest_threshold,
            })
            if theta == 1:
                curves.append({'u': u, 'b': b, 'z': z_grid.tolist(), 'cdf': cdf,
                               'poisson': poisson, 'y': y_grid.tolist(),
                               'exceedance_mark_cdf': mark})
    return {'rows': rows, 'curves': curves}


def conditional_sampler(u, samples, seed):
    """Exact exponential-tilt rejection for the stated finite model.

    Original R_j=u^2 E_j/j^2 are Exp(j^2/u^2). Tilted R_j have rate
    1+j^2/u^2. Set mu=E_t sum R_j. Accept a proposed vector iff S<=mu
    and U<=exp(S-mu). This produces the original law given S<=mu.
    No Gaussian replacement of a remainder is used.
    """
    rng = np.random.default_rng(seed)
    n = int(50 * u)
    gamma = np.arange(1, n + 1, dtype=float)
    rates = 1 + (gamma / u) ** 2
    scales = 1 / rates
    mu = float(scales.sum())
    variance = float(np.square(scales).sum())
    b = brentq(lambda w: float(np.exp(-rates * w).sum()) - 1, 1e-5, 100)
    accepted, proposals, arrays = 0, 0, []
    while accepted < samples:
        batch = 256
        values = rng.exponential(scales, size=(batch, n))
        sums = values.sum(axis=1)
        keep = (sums <= mu) & (np.log(rng.uniform(size=batch)) <= sums - mu)
        chosen = values[keep]
        if chosen.size:
            indices = chosen.argmax(axis=1)
            maxima = chosen[np.arange(len(chosen)), indices]
            winner_heights = (indices + 1) * math.sqrt(b) / u
            slack = mu - sums[keep]
            arrays.append(np.column_stack((maxima - b, winner_heights, slack)))
            accepted += len(chosen)
        proposals += batch
    observations = np.concatenate(arrays)[:samples]
    return {
        'spectrum': 'finite gamma_j=j, j=1,...,n; exact conditional sampling',
        'u': u, 'n': n, 'samples': samples, 'seed': seed, 'proposals': proposals,
        'acceptance': accepted / proposals, 'tilted_mean': mu,
        'tilted_variance': variance, 'b': b,
        'infinite_tilted_mean_minus_finite': (math.pi * u / math.tanh(math.pi*u)-1)/2-mu,
        'mean_slack': float(observations[:, 2].mean()),
        'mean_max_centered': float(observations[:, 0].mean()),
        'mean_winner_height_squared': float(np.square(observations[:, 1]).mean()),
        'correlation_matrix': np.corrcoef(observations.T).tolist(),
        'observations': observations.tolist(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--samples', type=int, default=6000)
    parser.add_argument('--skip-simulation', action='store_true')
    args = parser.parse_args()
    results = ROOT / 'results'
    results.mkdir(exist_ok=True)
    deterministic = deterministic_experiments()
    (results / 'asymptotic_diagnostics.json').write_text(
        json.dumps(deterministic, indent=2) + '\n')
    with (results / 'asymptotic_table.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(deterministic['rows'][0]))
        writer.writeheader()
        writer.writerows(deterministic['rows'])
    print('Completed 12 deterministic saddle/intensity checks.', flush=True)
    if not args.skip_simulation:
        simulations = []
        for k, u in enumerate((20.0, 80.0)):
            result = conditional_sampler(u, args.samples, 20261127+k)
            simulations.append(result)
            print(f"u={u:g}: {args.samples} exact finite conditional samples; "
                  f"acceptance={result['acceptance']:.4f}", flush=True)
        (results / 'conditional_simulation.json').write_text(
            json.dumps(simulations, indent=2) + '\n')
    print('These diagnostics do not certify the limiting theorem.', flush=True)


if __name__ == '__main__':
    main()
