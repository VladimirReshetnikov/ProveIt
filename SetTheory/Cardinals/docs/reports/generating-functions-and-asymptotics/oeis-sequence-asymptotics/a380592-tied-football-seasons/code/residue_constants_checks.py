#!/usr/bin/env python3
"""Numerical residue-class diagnostics from the limiting discrete Gaussian.

Rational centers fix the phases without floating-point reduction of large n.
The moments refer to delta = common score minus 8(n-1)/3, conditioned on all
scores being equal in the limiting law. They are numerical diagnostics;
no interval-certified error bound or asymptotic proof is claimed here.
"""

from fractions import Fraction
import math

from output_support import write_result

CENTERS = (Fraction(5, 28), Fraction(-13, 84), Fraction(43, 84))
SHIFT = Fraction(13, 84)
GAUSSIAN_RADIUS = 16
FOURIER_RADIUS = 8


def correction(delta):
    """Evaluate the report's exact rational first-correction polynomial."""
    return (
        Fraction(22180735, 45177216)
        + Fraction(98841, 153664) * delta
        - Fraction(5283, 3136) * delta**2
        - Fraction(9, 8) * delta**3
    )


def main():
    result = []
    for residue, center in enumerate(CENTERS):
        mean_phase = center + SHIFT
        samples = []
        for score in range(-GAUSSIAN_RADIUS, GAUSSIAN_RADIUS + 1):
            offset = Fraction(score) - center
            delta = Fraction(score) - mean_phase
            weight = math.exp(-float(Fraction(9, 4) * offset**2))
            samples.append((delta, weight))
        mass = math.fsum(weight for _, weight in samples)
        theta = 3 / (2 * math.sqrt(math.pi)) * mass
        fourier_theta = math.fsum(
            math.exp(-4 * math.pi**2 * j**2 / 9)
            * math.cos(2 * math.pi * j * float(center))
            for j in range(-FOURIER_RADIUS, FOURIER_RADIUS + 1)
        )
        first_correction = math.fsum(
            weight * float(correction(delta)) for delta, weight in samples
        ) / mass
        mean_delta = math.fsum(weight * float(delta) for delta, weight in samples) / mass
        variance_delta = math.fsum(
            weight * (float(delta) - mean_delta)**2 for delta, weight in samples
        ) / mass
        assert math.isclose(theta, fourier_theta, rel_tol=2e-14, abs_tol=0.0)
        assert variance_delta > 0
        result.append({
            "n_mod_3": residue,
            "center": str(center),
            "mu_phase": str(mean_phase),
            "theta_gaussian_sum": theta,
            "theta_fourier_sum": fourier_theta,
            "first_relative_correction": first_correction,
            "conditional_mean_delta": mean_delta,
            "conditional_variance_delta": variance_delta,
        })
    print(write_result("residue_constants_checks", {
        "gaussian_sum_radius": GAUSSIAN_RADIUS,
        "fourier_sum_radius": FOURIER_RADIUS,
        "residues": result,
    }))


if __name__ == "__main__":
    main()
