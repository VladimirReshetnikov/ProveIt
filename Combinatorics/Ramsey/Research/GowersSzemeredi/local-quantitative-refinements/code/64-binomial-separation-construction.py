#!/usr/bin/env python3
"""Exact finite components of the binomial-separation construction.

Only the Python standard library is required. The circle input coloring is
supplied by the caller; this module does not implement the Shi--Dong coloring
at its enormous theoretical sizes, or certify analytic limiting assertions.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import comb, factorial, prod
from typing import Iterable, Sequence


SEED_SIX = (0, 1, 4, 13)
BASE_SIX = 80
WEIGHTS_SIX = (1, 5, 10)
SEED_FOUR = (0, 1, 2)
BASE_FOUR = 9
WEIGHTS_FOUR = (1, 3)


def binomial_coefficients(k: int) -> tuple[int, ...]:
    """Coefficients of the (k-1)-st finite-difference equation."""
    if k < 2:
        raise ValueError("k must be at least 2")
    return tuple((-1) ** i * comb(k - 1, i) for i in range(k))


def separation_certificate(
    alphabet: Sequence[int], weights: Sequence[int], modulus: int
) -> list[dict[str, object]]:
    """Certify injectivity by enumerating ordered tuples.

    Complexity is |alphabet|**len(weights); intended for finite certificates,
    not large-scale constructions. Raises ValueError with a collision witness.
    """
    if modulus < 1 or not alphabet or not weights:
        raise ValueError("positive modulus, nonempty alphabet and weights required")
    if any(w <= 0 for w in weights):
        raise ValueError("weights must be positive")
    residues = [x % modulus for x in alphabet]
    if len(set(residues)) != len(alphabet):
        raise ValueError("alphabet has repeated residues")
    seen: dict[int, tuple[int, ...]] = {}
    certificate: list[dict[str, object]] = []
    for entries in product(alphabet, repeat=len(weights)):
        image = sum(w * x for w, x in zip(weights, entries)) % modulus
        if image in seen:
            raise ValueError(
                f"collision modulo {modulus}: {seen[image]} and {entries} -> {image}"
            )
        seen[image] = entries
        certificate.append({"tuple": list(entries), "residue": image})
    return certificate


def digit_lift(alphabet: Sequence[int], base: int, layers: int) -> tuple[int, ...]:
    """Build all nonnegative integers with the specified finite digit strings."""
    if base < 2 or layers < 0:
        raise ValueError("base >= 2 and layers >= 0 required")
    if not alphabet or len(set(alphabet)) != len(alphabet):
        raise ValueError("alphabet must be nonempty with distinct digits")
    if any(d < 0 or d >= base for d in alphabet):
        raise ValueError("digits must lie in [0, base)")
    values = [0]
    for _ in range(layers):
        values = [d + base * x for x in values for d in alphabet]
    return tuple(sorted(values))


def labels(k: int, size: int) -> tuple[int, tuple[int, ...]]:
    """Return an explicit mirror-separating modulus and `size` labels.

    Supported lengths are four and six. Selection of the power uses integer
    arithmetic, so floating-point logarithms cannot select the wrong layer.
    """
    if size < 1:
        raise ValueError("size must be positive")
    if k == 4:
        seed, base = SEED_FOUR, BASE_FOUR
    elif k == 6:
        seed, base = SEED_SIX, BASE_SIX
    else:
        raise ValueError("only k=4 and k=6 have certified seeds in this package")
    capacity = 1
    layer_count = 0
    while capacity < size:
        capacity *= len(seed)
        layer_count += 1
    return base**layer_count, digit_lift(seed, base, layer_count)[:size]


def slice_constant(k: int) -> Fraction:
    """Evaluate the normalized binomial slice volume, exactly.

    Uses the 2**k-term truncated-power formula. Appropriate for moderate k.
    """
    if k < 4 or k % 2:
        raise ValueError("an even k >= 4 is required")
    c = binomial_coefficients(k)
    weights = tuple(x for x in c if x > 0)
    repeated = weights + weights
    center = sum(weights)
    numerator = 0
    for chosen in product((0, 1), repeat=k):
        offset = sum(w * b for w, b in zip(repeated, chosen))
        numerator += (-1) ** sum(chosen) * max(0, center - offset) ** (k - 1)
    denominator = factorial(k - 1) * prod(repeated)
    return Fraction(numerator, denominator)


def symmetric_progression_free(colors: Sequence[int], k: int) -> bool:
    """Exhaustive check of the finite interval hypothesis (not a cyclic test)."""
    if k < 4 or k % 2 or not colors:
        raise ValueError("an even k >= 4 and a nonempty coloring are required")
    n = len(colors)
    for step in range(1, (n - 1) // (k - 1) + 1):
        for start in range(n - (k - 1) * step):
            pattern = tuple(colors[start + i * step] for i in range(k))
            if pattern == pattern[::-1]:
                return False
    return True


@dataclass(frozen=True)
class TorusConstruction:
    """Finite exact description of the rectangle-union construction.

    Setting check_coloring=True verifies the interval hypothesis exhaustively;
    use that only on manageable input colorings. The constructor always uses
    the proved four- or six-variable label seeds.
    """

    k: int
    colors: tuple[int, ...]
    density: Fraction
    palette_size: int
    modulus: int
    label_values: tuple[int, ...]

    @classmethod
    def from_coloring(
        cls, k: int, colors: Iterable[int], density: Fraction,
        *, check_coloring: bool = True,
    ) -> "TorusConstruction":
        color_tuple = tuple(colors)
        if k not in (4, 6):
            raise ValueError("k must be four or six")
        if not color_tuple or any(not isinstance(c, int) or c < 0 for c in color_tuple):
            raise ValueError("colors must be a nonempty sequence of nonnegative integers")
        if not isinstance(density, Fraction):
            raise TypeError("density must be a fractions.Fraction")
        palette = max(color_tuple) + 1
        modulus, label_values = labels(k, 9 * palette)
        if density <= 0 or density > Fraction(1, 2 ** (k - 2) * modulus):
            raise ValueError("density must satisfy 0 < alpha <= 1/(W_k * modulus)")
        if check_coloring and not symmetric_progression_free(color_tuple, k):
            raise ValueError("the supplied coloring contains a nonconstant symmetric progression")
        return cls(k, color_tuple, density, palette, modulus, label_values)

    def color_at(self, x: Fraction) -> int:
        """Circle color at a rational coordinate, with half-open endpoints."""
        x = x % 1
        n = len(self.colors)
        cell = (9 * n * x.numerator) // x.denominator
        a, rest = divmod(cell, 3 * n)
        b, c = divmod(rest, 3)
        return (3 * a + c) * self.palette_size + self.colors[b]

    def contains(self, n: int, prime_modulus: int) -> bool:
        """Membership in A_P using exact modular and integer arithmetic.

        The limiting theorem assumes prime P. Primality is the caller's
        responsibility; no potentially expensive or probabilistic primality
        test is silently performed here.
        """
        if prime_modulus <= self.k:
            raise ValueError("the final modulus must exceed k")
        p = prime_modulus
        n %= p
        color = self.color_at(Fraction(n, p))
        label = self.label_values[color]
        y = pow(n, self.k - 2, p)
        delta = y * self.modulus - label * p
        return (delta >= 0 and
                delta * self.density.denominator <
                self.density.numerator * self.modulus * p)

    def reduced_count(self) -> Fraction:
        """Exact torus progression integral from the mathematical theorem."""
        return (slice_constant(self.k) * self.density ** (self.k - 1) /
                (9 * (self.k - 1) * len(self.colors)))
