"""Canonical finite-stage Kraft allocation for dyadic probability increments."""
from __future__ import annotations
from fractions import Fraction


class PrefixAllocator:
    def __init__(self):
        self.free: list[str] = [""]
        self.allocated: dict[str, str] = {}

    def request(self, length: int, label: str) -> str:
        if type(length) is not int or length < 0:
            raise ValueError("Code length must be a nonnegative integer")
        choices = [w for w in self.free if len(w) <= length]
        if not choices:
            raise ValueError("Insufficient free Kraft mass for this request")
        # At most one free word has each length; lexicographic fallback is explicit.
        word = sorted(choices, key=lambda w: (-len(w), w))[0]
        self.free.remove(word)
        while len(word) < length:
            self.free.append(word + "1")
            word += "0"
        self.allocated[word] = label
        return word

    def add_dyadic(self, mass: Fraction, label: str) -> list[str]:
        if not isinstance(mass, Fraction) or mass < 0:
            raise ValueError("Mass must be a nonnegative Fraction")
        denominator = mass.denominator
        if denominator & (denominator - 1):
            raise ValueError("Mass must be dyadic")
        if mass + self.total() > 1:
            raise ValueError("Total allocated mass would exceed one")
        if mass > 1:
            raise ValueError("Mass cannot exceed one")
        n = denominator.bit_length() - 1
        out = []
        for j in reversed(range(mass.numerator.bit_length())):
            if (mass.numerator >> j) & 1:
                out.append(self.request(n-j, label))
        return out

    def total(self, label: str | None = None) -> Fraction:
        return sum((Fraction(1, 1 << len(w)) for w,l in self.allocated.items()
                    if label is None or l == label), Fraction(0))

    def check(self) -> None:
        words = list(self.allocated) + self.free
        assert len(words) == len(set(words))
        for i, w in enumerate(words):
            for j, z in enumerate(words):
                if i != j:
                    assert not z.startswith(w)
        assert len({len(w) for w in self.free}) == len(self.free)
        assert sum((Fraction(1, 1 << len(w)) for w in words), Fraction(0)) == 1
