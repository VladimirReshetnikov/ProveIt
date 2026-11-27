#!/usr/bin/env python3
"""Finite jump-band implementation of the arithmetic decoder.

Input ordinates are signed and repeated with their multiplicities. The finite
simulation is an illustration, not a proof or a certification of any zero.
For a symmetrized jump measure a single listed ordinate contributes total
intensity 1, split equally between its positive and negative Cayley angles.
The cosine statistic depends only on the magnitude, so the two counts can be
combined into one Poisson count of mean duration.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np


def cayley_angle(gamma):
    gamma = np.asarray(gamma, dtype=float)
    if np.any(gamma == 0):
        raise ValueError("The band decoder excludes central zeros.")
    return 2 * np.arctan(1 / (2 * np.abs(gamma)))


def ordinate_from_jump(jump):
    jump = np.asarray(jump, dtype=float)
    if np.any((np.abs(jump) <= 0) | (np.abs(jump) > np.pi)):
        raise ValueError("Jump magnitude must belong to (0, pi].")
    return 1 / (2 * np.tan(np.abs(jump) / 2))


def band_weights(signed_ordinates, height, primes):
    """Return one decoder weight per prime and per signed zero in (T,2T]."""
    if height <= 0:
        raise ValueError("height must be positive")
    gammas = np.asarray(signed_ordinates, dtype=float)
    gammas = np.abs(gammas[(np.abs(gammas) > height) &
                            (np.abs(gammas) <= 2 * height)])
    primes = np.asarray(primes, dtype=float)
    if np.any(primes <= 1):
        raise ValueError("Probe bases must exceed 1; the theorem uses primes.")
    coefficients = -np.pi * np.sqrt(primes) / (height * np.log(primes))
    return gammas, coefficients[:, None] * np.cos(np.log(primes)[:, None] * gammas)


def exact_finite_moments(signed_ordinates, duration, height, primes):
    """Analytic mean/covariance for the finite atomic Poisson model."""
    if duration <= 0:
        raise ValueError("duration must be positive")
    gammas, weights = band_weights(signed_ordinates, height, primes)
    return weights.sum(axis=1), (weights @ weights.T) / duration, len(gammas)


def simulate_band(signed_ordinates, duration, height, primes,
                  replicates=1000, seed=20261127):
    """Simulate decoder statistics; rows are independent paths."""
    if duration <= 0 or replicates <= 0:
        raise ValueError("positive duration and replicate count required")
    gammas, weights = band_weights(signed_ordinates, height, primes)
    rng = np.random.default_rng(seed)
    counts = rng.poisson(duration, size=(replicates, len(gammas)))
    return (counts @ weights.T) / duration


def decode_observed_jumps(jumps, duration, height, primes):
    """Apply the theorem's statistic to an observed finite list of jumps."""
    if duration <= 0:
        raise ValueError("duration must be positive")
    gammas = ordinate_from_jump(jumps)
    gammas = gammas[(gammas > height) & (gammas <= 2 * height)]
    p = np.asarray(primes, dtype=float)
    return (-np.pi * np.sqrt(p) / (duration * height * np.log(p))) * (
        np.cos(np.log(p)[:, None] * gammas).sum(axis=1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path(__file__).resolve().parents[1] / "data/zeta_first_150.json")
    parser.add_argument("--duration", type=float, default=1.0)
    parser.add_argument("--height", type=float, default=128.0)
    parser.add_argument("--replicates", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=20261127)
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    positive = np.array([float(z["gamma"]) for z in data["zeros"]])
    if positive.max() <= 2 * args.height:
        raise ValueError("The supplied zeta table does not extend beyond the band.")
    signed = np.r_[-positive, positive]
    primes = [2, 3, 5]
    mean, covariance, atoms = exact_finite_moments(signed, args.duration, args.height, primes)
    draws = simulate_band(signed, args.duration, args.height, primes, args.replicates, args.seed)
    out = {
        "status": "Numerical illustration; zero data are not interval-certified.",
        "height": args.height, "duration": args.duration,
        "signed_zero_count_in_band": atoms,
        "primes": primes, "target_real_character_values_for_zeta": [1, 1, 1],
        "exact_finite_model_mean": mean.tolist(),
        "exact_finite_model_covariance": covariance.tolist(),
        "simulation_mean": draws.mean(axis=0).tolist(),
        "simulation_covariance": np.cov(draws, rowvar=False).tolist(),
        "asymptotic_covariance_diagonal": [float(np.pi * p / (2 * args.duration * np.log(p)**2) * np.log(args.height) / args.height) for p in primes],
        "replicates": args.replicates, "seed": args.seed,
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
