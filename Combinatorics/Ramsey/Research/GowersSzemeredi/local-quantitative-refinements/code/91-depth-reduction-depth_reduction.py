"""Explicit, optimally sparse critical-depth phase reduction.

Only standard-library modules are required. Polynomial-degree hypotheses are
mathematical preconditions, not inferred by the numerical selector.
All averages are normalized. Phase values are supplied as exact integer
residues modulo p**(a+1), after subtracting a constant phase.
"""
from __future__ import annotations

from dataclasses import dataclass
from cmath import exp
from math import pi, sin, isfinite
from typing import Iterable, Sequence


def is_prime(p: int) -> bool:
    if isinstance(p, bool) or not isinstance(p, int) or p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def validate_parameters(p: int, a: int) -> None:
    if not is_prime(p):
        raise ValueError("p must be prime")
    if isinstance(a, bool) or not isinstance(a, int) or a < 1:
        raise ValueError("a must be a positive integer")


def transfer_constant(p: int, a: int) -> float:
    """sin(pi/p**a)/(p*sin(pi/p**(a+1))); ordinary double precision."""
    validate_parameters(p, a)
    m = p**a
    return sin(pi / m) / (p * sin(pi / (p * m)))


def atoms(p: int, a: int) -> list[list[complex]]:
    """a_j(t)=exp(-2 pi i 1_{t<j}/p**a), with 0<=j,t<p."""
    validate_parameters(p, a)
    omega_inv = exp(-2j * pi / p**a)
    return [[omega_inv if t < j else 1.0 + 0j for t in range(p)]
            for j in range(p)]


def digit_phase(p: int, a: int) -> list[complex]:
    validate_parameters(p, a)
    return [exp(2j * pi * t / p**(a + 1)) for t in range(p)]


def inner(f: Sequence[complex], g: Sequence[complex]) -> complex:
    if len(f) != len(g) or not f:
        raise ValueError("vectors must have the same positive length")
    return sum(x * y.conjugate() for x, y in zip(f, g)) / len(f)


def cyclic_scores(f: Sequence[complex], p: int, a: int) -> list[complex]:
    """All p normalized atom correlations in O(p) arithmetic operations."""
    validate_parameters(p, a)
    if len(f) != p:
        raise ValueError("f must have exactly p entries")
    omega = exp(2j * pi / p**a)
    total = sum(f) / p
    prefix = 0j
    scores = []
    for t in range(p):
        scores.append(total + (omega - 1) * prefix)
        prefix += f[t] / p
    return scores


@dataclass(frozen=True)
class ReductionResult:
    p: int
    depth: int
    chosen_index: int
    original_correlation: complex
    candidate_correlations: tuple[complex, ...]
    theoretical_factor: float
    total_weight: float

    @property
    def selected_correlation(self) -> complex:
        return self.candidate_correlations[self.chosen_index]

    def phase_residue(self, original_residue: int) -> int:
        """Selected phase, now modulo p**a (one less depth)."""
        if isinstance(original_residue, bool) or not isinstance(original_residue, int):
            raise TypeError("phase residue must be an integer")
        m = self.p**self.depth
        r = original_residue % (self.p * m)
        return (r // self.p - int(r % self.p < self.chosen_index)) % m


def reduce_samples(samples: Iterable[tuple[int, complex, float]],
                   p: int, a: int) -> ReductionResult:
    """Select a lower-depth phase from weighted samples in O(N+p) time.

    Each sample is (r, f_value, weight), where P(x)=r/p**(a+1) modulo 1,
    and weights are finite nonnegative real numbers.
    A critical-degree polynomial P has linear r mod p and produces genuine
    lower-depth polynomial candidates. For arbitrary residues, the returned
    numerical correlation inequality still holds, but polynomiality is NOT
    guaranteed. Input f need not be bounded, but must be finite.
    """
    validate_parameters(p, a)
    m = p**a
    M = p * m
    slice_sums = [0j] * p
    total_weight = 0.0
    original_sum = 0j
    for r, value, weight in samples:
        if isinstance(r, bool) or not isinstance(r, int):
            raise TypeError("phase residues must be integers")
        z = complex(value)
        w = float(weight)
        if not (isfinite(z.real) and isfinite(z.imag)):
            raise ValueError("function values must be finite")
        if not isfinite(w) or w < 0:
            raise ValueError("weights must be finite and nonnegative")
        r %= M
        t = r % p
        q = r // p
        slice_sums[t] += w * z * exp(-2j * pi * q / m)
        original_sum += w * z * exp(-2j * pi * r / M)
        total_weight += w
    if not isfinite(total_weight) or total_weight <= 0:
        raise ValueError("total weight must be finite and positive")
    if not all(isfinite(z.real) and isfinite(z.imag)
               for z in [original_sum, *slice_sums]):
        raise ValueError("weighted sums overflowed; rescale values or weights")
    # slice_sums/total_weight are mass-weighted, not conditional, averages.
    mass = [z / total_weight for z in slice_sums]
    total = sum(mass)
    omega = exp(2j * pi / m)
    prefix = 0j
    scores = []
    for t in range(p):
        scores.append(total + (omega - 1) * prefix)
        prefix += mass[t]
    if not all(isfinite(z.real) and isfinite(z.imag) for z in scores):
        raise ValueError("score calculation overflowed; rescale function values")
    chosen = max(range(p), key=lambda j: abs(scores[j]))
    return ReductionResult(p, a, chosen, original_sum / total_weight,
                           tuple(scores), transfer_constant(p, a), total_weight)


if __name__ == "__main__":
    p, a = 3, 1
    f = digit_phase(p, a)
    result = reduce_samples(((t, f[t], 1.0) for t in range(p)), p, a)
    print(f"p={p}, a={a}, c={result.theoretical_factor:.15f}")
    print(f"original={abs(result.original_correlation):.15f}")
    print(f"selected={abs(result.selected_correlation):.15f}")
    print(f"index={result.chosen_index}")
