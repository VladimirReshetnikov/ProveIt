"""Exact root-level spectral core for increasing polynomial iterative equations.

This implementation accepts Gaussian-rational roots, not arbitrary coefficient
polynomials. Conjugate roots must both be present with equal multiplicities.
All modulus comparisons use exact squared moduli (fractions.Fraction).
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Mapping

@dataclass(frozen=True, order=True)
class Root:
    re: Fraction
    im: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, 're', Fraction(self.re))
        object.__setattr__(self, 'im', Fraction(self.im))

    @property
    def modulus_squared(self) -> Fraction:
        return self.re*self.re + self.im*self.im

    @property
    def is_positive(self) -> bool:
        return self.im == 0 and self.re > 0

    def conjugate(self) -> Root:
        return Root(self.re, -self.im)

ONE = Root(Fraction(1))
Spectrum = dict[Root, int]

def validate(spectrum: Mapping[Root, int]) -> Spectrum:
    out = dict(spectrum)
    for root, multiplicity in out.items():
        if not isinstance(root, Root):
            raise TypeError('Keys must be Root instances.')
        if not isinstance(multiplicity, int) or isinstance(multiplicity, bool) or multiplicity <= 0:
            raise ValueError('Multiplicities must be positive integers.')
        if root.modulus_squared == 0:
            raise ValueError('The constant coefficient must be nonzero.')
        if out.get(root.conjugate()) != multiplicity:
            raise ValueError('Conjugate roots must have equal multiplicities.')
    return out

def difference_spectrum(spectrum: Mapping[Root, int]) -> Spectrum:
    """Remove exactly one occurrence of the root 1, if it is present."""
    out = validate(spectrum)
    if ONE in out:
        out[ONE] -= 1
        if not out[ONE]:
            del out[ONE]
    return out

def positive_admissible(spectrum: Mapping[Root, int]) -> bool:
    """Test the theorem's positive bilateral-recurrence criterion."""
    s = validate(spectrum)
    if not s:
        return False  # the zero-degree polynomial kills only the zero sequence
    radii = sorted({z.modulus_squared for z in s})
    for radius in {radii[0], radii[-1]}:
        on_circle = {z: m for z, m in s.items() if z.modulus_squared == radius}
        positive = [z for z in on_circle if z.is_positive]
        if len(positive) != 1:
            return False
        multiplicity = s[positive[0]]
        if multiplicity < max(on_circle.values()):
            return False
        if len(radii) == 1 and multiplicity % 2 == 0:
            return False
    return True

def realizable(spectrum: Mapping[Root, int]) -> bool:
    """Whether this is exactly the minimal polynomial of an increasing map."""
    s = validate(spectrum)
    if s == {ONE: 1}:
        return True
    return positive_admissible(difference_spectrum(s))

def positive_core(spectrum: Mapping[Root, int]) -> Spectrum:
    """Largest positive-admissible divisor, or {} if there is none."""
    s = validate(spectrum)
    positive = sorted(z for z in s if z.is_positive)
    if not positive:
        return {}
    if len(positive) == 1:
        r = positive[0]
        cap = s[r] if s[r] % 2 else s[r] - 1
        return {z: min(m, cap) for z, m in s.items()
                if z.modulus_squared == r.modulus_squared}
    lo, hi = positive[0], positive[-1]
    a, b = lo.modulus_squared, hi.modulus_squared
    out: Spectrum = {}
    for z, m in s.items():
        q = z.modulus_squared
        if a < q < b:
            out[z] = m
        elif q == a:
            out[z] = min(m, s[lo])
        elif q == b:
            out[z] = min(m, s[hi])
    return out

def increasing_core(spectrum: Mapping[Root, int]) -> Spectrum:
    """Minimal universal annihilator; {} denotes no increasing solutions."""
    s = validate(spectrum)
    out = positive_core(difference_spectrum(s))
    if ONE in s:
        out[ONE] = out.get(ONE, 0) + 1
    return out

def fixed_point_realizable(spectrum: Mapping[Root, int]) -> bool:
    s = validate(spectrum)
    if s == {ONE: 1}:
        return True
    if not s or s.get(ONE, 0) > 1:
        return False
    if any(z != ONE and z.modulus_squared == 1 for z in s):
        return False
    below = {z:m for z,m in s.items() if z.modulus_squared < 1}
    above = {z:m for z,m in s.items() if z.modulus_squared > 1}
    return bool(below or above) and all(positive_admissible(t) for t in (below, above) if t)

def fixed_point_free_realizable(spectrum: Mapping[Root, int]) -> bool:
    s = validate(spectrum)
    if not realizable(s) or s == {ONE:1}:
        return False
    d = difference_spectrum(s)
    return min(z.modulus_squared for z in d) <= 1 <= max(z.modulus_squared for z in d)

def affine_rigid(spectrum: Mapping[Root, int]) -> bool:
    """Nonvacuous: require at least one increasing solution."""
    c = increasing_core(spectrum)
    if c == {ONE:2}:
        return True
    return len(c) == 1 and next(iter(c)).is_positive and next(iter(c.values())) == 1
