#!/usr/bin/env python3
"""Construct the positive filters proved in the accompanying research note.

Numerical construction uses mpmath; it is not a certified zero finder.
The mathematical construction is exact when its frequency inputs are exact.
"""
from __future__ import annotations

from dataclasses import dataclass
import mpmath as mp


def sinc(x):
    return mp.mpf(1) if not x else mp.sin(x) / x


def color_frequencies(positive_frequencies, delta=1):
    """Greedy optimal coloring of interval conflicts; retains repetitions."""
    delta = mp.mpf(delta)
    if delta <= 0:
        raise ValueError("delta must be positive.")
    frequencies = sorted(mp.mpf(x) for x in positive_frequencies)
    if any(x < delta for x in frequencies):
        raise ValueError("Each positive frequency must be at least delta.")
    colors = []
    for frequency in frequencies:
        for color in colors:
            if frequency - color[-1] >= delta:
                color.append(frequency)
                break
        else:
            colors.append([frequency])
    return colors


@dataclass
class SeparatedFilter:
    positive: list
    delta: object = 1
    radius: object = None

    def __post_init__(self):
        self.delta = mp.mpf(self.delta)
        if self.delta <= 0:
            raise ValueError("delta must be positive.")
        self.radius = 4 * mp.pi / self.delta if self.radius is None else mp.mpf(self.radius)
        if self.radius * self.delta < 4 * mp.pi:
            raise ValueError("The proof requires radius * delta >= 4*pi.")
        positive = sorted(mp.mpf(x) for x in self.positive)
        if not positive or positive[0] < self.delta:
            raise ValueError("Supply a nonempty positive set separated from zero.")
        if any(b-a < self.delta for a, b in zip(positive, positive[1:])):
            raise ValueError("Frequencies are not delta-separated.")
        self.positive = positive
        self.frequencies = sorted([-x for x in positive] + positive)
        self.matrix = mp.matrix([[self.base_transform(x-y) for y in self.frequencies]
                                 for x in self.frequencies])
        self.rhs = mp.matrix([self.base_transform(x) for x in self.frequencies])
        self.coefficients = mp.lu_solve(self.matrix, -self.rhs)
        for i in range(len(self.frequencies)//2):
            j = len(self.frequencies)-1-i
            average = (self.coefficients[i]+self.coefficients[j])/2
            self.coefficients[i] = self.coefficients[j] = average
        self.mass = 1 + mp.fsum(a*self.base_transform(x)
                              for a, x in zip(self.coefficients, self.frequencies))

    def base_transform(self, frequency):
        return sinc(self.radius * frequency / 2) ** 2

    def transform(self, frequency):
        return (self.base_transform(frequency) + mp.fsum(
            a*self.base_transform(frequency-x)
            for a, x in zip(self.coefficients, self.frequencies))) / self.mass

    def density_ratio(self, t):
        """Density divided by the triangular density, extended to endpoints."""
        return (1 + mp.fsum(a*mp.cos(x*t) for a, x in
                            zip(self.coefficients, self.frequencies))) / self.mass

    def density(self, t):
        return max(mp.mpf(0), 1-abs(t)/self.radius)/self.radius*self.density_ratio(t)

    def diagnostics(self):
        n = len(self.frequencies)
        off_diagonal = max(mp.fsum(abs(self.matrix[i,j]) for i in range(n) if i != j)
                           for j in range(n))
        residual = self.matrix*self.coefficients + self.rhs
        return {
            "points": n,
            "radius": str(self.radius),
            "off_diagonal_norm_1": str(off_diagonal),
            "rhs_norm_1": str(mp.fsum(abs(x) for x in self.rhs)),
            "coefficient_norm_1": str(mp.fsum(abs(x) for x in self.coefficients)),
            "normalizing_mass": str(self.mass),
            "linear_residual_max": str(max(abs(x) for x in residual)),
            "root_residual_max": str(max(abs(self.transform(x)) for x in self.frequencies)),
        }


class PositiveFilter:
    def __init__(self, positive_frequencies, cutoff, delta=1, damping_count=None):
        self.cutoff = mp.mpf(cutoff)
        if self.cutoff <= 0:
            raise ValueError("cutoff must be positive.")
        self.delta = mp.mpf(delta)
        self.colors = color_frequencies(positive_frequencies, delta)
        self.factors = [SeparatedFilter(c, delta) for c in self.colors]
        self.damping_count = int(mp.ceil(self.cutoff*mp.log(self.cutoff))) if damping_count is None else int(damping_count)
        if self.cutoff <= 0 or self.damping_count < 0:
            raise ValueError("Positive cutoff and nonnegative damping count required.")
        self.radius = mp.fsum(f.radius for f in self.factors) + self.damping_count/self.cutoff

    def low_transform(self, frequency):
        return mp.fprod(f.transform(frequency) for f in self.factors)

    def transform(self, frequency):
        return self.low_transform(frequency)*sinc(frequency/self.cutoff)**self.damping_count

    @property
    def tail_bound(self):
        return mp.sin(1)**self.damping_count

