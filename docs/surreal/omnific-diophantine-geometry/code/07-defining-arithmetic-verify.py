#!/usr/bin/env python3
"""Exact, reproducible finite checks for article.tex (Python 3.10+).

No third-party dependencies; no floating-point calculations.
This is not a formal proof of the Hahn-series or logical theorems.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isqrt
from typing import Dict, Tuple, Union

Exponent = Tuple[int, ...]


@dataclass
class Poly:
    """Finite Laurent polynomials with z_0^2 = radicand.

    The remaining variables are independent; negative exponents are
    allowed there, so c^{-1} can be treated formally. Coefficients are
    integers. Every operation normalizes into a finite exact dictionary.
    """

    terms: Dict[Exponent, int]
    nvars: int = 4
    radicand: int = 13

    def __post_init__(self) -> None:
        normalized: Dict[Exponent, int] = {}
        for e, coefficient in self.terms.items():
            if len(e) != self.nvars or e[0] < 0:
                raise ValueError("Invalid exponent vector")
            exponent = (e[0] % 2,) + e[1:]
            value = coefficient * self.radicand ** (e[0] // 2)
            normalized[exponent] = normalized.get(exponent, 0) + value
        self.terms = {e: c for e, c in normalized.items() if c != 0}

    @classmethod
    def constant(cls, value: int, nvars: int = 4, radicand: int = 13) -> Poly:
        return cls({(0,) * nvars: value}, nvars, radicand)

    @classmethod
    def variable(cls, index: int, exponent: int = 1,
                 nvars: int = 4, radicand: int = 13) -> Poly:
        if not 0 <= index < nvars:
            raise ValueError("Variable index outside the ring")
        e = [0] * nvars
        e[index] = exponent
        return cls({tuple(e): 1}, nvars, radicand)

    def coerce(self, other: Union[Poly, int]) -> Poly:
        if isinstance(other, int):
            return Poly.constant(other, self.nvars, self.radicand)
        if not isinstance(other, Poly):
            raise TypeError("Expected an integer or polynomial")
        if (self.nvars, self.radicand) != (other.nvars, other.radicand):
            raise ValueError("Incompatible polynomial rings")
        return other

    def __add__(self, other: Union[Poly, int]) -> Poly:
        other = self.coerce(other)
        terms = dict(self.terms)
        for e, c in other.terms.items():
            terms[e] = terms.get(e, 0) + c
        return Poly(terms, self.nvars, self.radicand)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({e: -c for e, c in self.terms.items()},
                    self.nvars, self.radicand)

    def __sub__(self, other: Union[Poly, int]) -> Poly:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Union[Poly, int]) -> Poly:
        return self.coerce(other) + (-self)

    def __mul__(self, other: Union[Poly, int]) -> Poly:
        other = self.coerce(other)
        terms: Dict[Exponent, int] = {}
        for e, a in self.terms.items():
            for f, b in other.terms.items():
                g = tuple(x + y for x, y in zip(e, f))
                terms[g] = terms.get(g, 0) + a * b
        return Poly(terms, self.nvars, self.radicand)

    __rmul__ = __mul__

    def __pow__(self, n: int) -> Poly:
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only nonnegative integer powers are implemented")
        result = Poly.constant(1, self.nvars, self.radicand)
        base = self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, (int, Poly)):
            return False
        other = self.coerce(other)
        return self.terms == other.terms

    def at_zero(self, index: int) -> Poly:
        if any(e[index] < 0 for e in self.terms):
            raise ValueError("Cannot set an inverted variable to zero")
        return Poly({e: c for e, c in self.terms.items() if e[index] == 0},
                    self.nvars, self.radicand)


def P(t):
    return (t * t - 13) * (t * t - 17) * (t * t - 221)


def p_mod(t: int, modulus: int) -> int:
    y = t * t % modulus
    return ((y - 13) * (y - 17) * (y - 221)) % modulus


def root_mod(modulus: int) -> int:
    if modulus <= 0:
        raise ValueError("Modulus must be positive")
    for t in range(modulus):
        if p_mod(t, modulus) == 0:
            return t
    raise AssertionError(f"No root found modulo {modulus}")


def pell(n: int) -> Tuple[int, int]:
    if n < 0:
        raise ValueError("Negative Pell index")
    u, v = 1, 0
    for _ in range(n):
        u, v = 3 * u + 4 * v, 2 * u + 3 * v
    return u, v


def return_index(modulus: int) -> int:
    u, v = 1 % modulus, 0
    for n in range(1, modulus * modulus + 1):
        u, v = (3 * u + 4 * v) % modulus, (2 * u + 3 * v) % modulus
        if (u, v) == (1 % modulus, 0):
            return n
    raise AssertionError(f"No return by m^2 for m={modulus}")


def four_squares(n: int) -> Tuple[int, int, int, int]:
    if n < 0:
        raise ValueError("Negative four-square input")
    pairs: Dict[int, Tuple[int, int]] = {}
    for a in range(isqrt(n) + 1):
        for b in range(a, isqrt(n - a * a) + 1):
            pairs.setdefault(a * a + b * b, (a, b))
    for subtotal, pair in pairs.items():
        if n - subtotal in pairs:
            return pair + pairs[n - subtotal]
    raise AssertionError(f"No four-square representation of {n}")


Gaussian = Tuple[int, int]


def gmul(x: Gaussian, y: Gaussian) -> Gaussian:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c


def main() -> None:
    print("Defining Arithmetic Inside Omnific Integers")
    print("Exact finite and symbolic checks; no floating-point arithmetic.")
    print("These checks are not a formal verification of the article.\n")

    # Polynomial identity in Z[r,b,c,c^{-1},X]/(r^2-13).
    r, b, c, X = (Poly.variable(j) for j in range(4))
    ci = Poly.variable(2, -1)
    expanded = P(X)
    expected = X ** 6 - 251 * X ** 4 + 6851 * X ** 2 - 48841
    assert expanded == expected
    assert P(0) == -48841 and P(1) == -42240
    print("PASS: P expansion and P(0), P(1).")

    a = c + X
    alpha = (b - r) * ci
    t = r + alpha * a
    s = alpha * (2 * r + alpha * a) * (t ** 2 - 17) * (t ** 2 - 221)
    assert a * s == P(t)
    assert t.at_zero(3) == b
    assert s.at_zero(3) == P(b) * ci
    assert max(e[3] for e in t.terms) == 1
    assert max(e[3] for e in s.terms) == 5
    print("PASS: universal witness identity a*s=P(t), c0(t)=b, c0(s)=P(b)/c.")
    print("      Symbolic ring: Z[r,b,c,c^{-1},X]/(r^2-13), a=c+X.")
    print("PASS: polynomial witness degrees in X are 1 and 5.")

    te = -r * X
    se = 13 * (X - 1) * (13 * X ** 2 - 17) * (13 * X ** 2 - 221)
    assert (1 + X) * se == P(te)
    assert te.at_zero(3) == 0 and se.at_zero(3) == -48841
    print("PASS: explicit certificate for 1+omega.")

    max_root = (0, 1)
    for modulus in range(1, 4097):
        root = root_mod(modulus)
        assert P(root) % modulus == 0
        if root > max_root[0]:
            max_root = (root, modulus)
    print("PASS: P has a root modulo every m from 1 through 4096.")
    print(f"      Largest first nonnegative root in this run: {max_root[0]} "
          f"(mod {max_root[1]}).")

    # Separately test the exceptional 2-adic lifting used in the proof.
    root = 1
    for e in range(3, 33):
        assert (root * root - 17) % (2 ** e) == 0
        if (root * root - 17) % (2 ** (e + 1)):
            root += 2 ** (e - 1)
        assert (root * root - 17) % (2 ** (e + 1)) == 0
    print("PASS: the quadratic 2-adic lifting step through modulus 2^33.")

    for n in range(301):
        u, v = pell(n)
        assert u * u - 2 * v * v == 1
        assert u >= 3 ** n
        if n:
            assert v > 0
    max_return = (0, 1)
    for modulus in range(1, 501):
        n = return_index(modulus)
        assert 1 <= n <= modulus * modulus
        u, v = pell(n)
        assert u % modulus == 1 % modulus and v % modulus == 0 and v > 0
        if n > max_return[0]:
            max_return = (n, modulus)
    print("PASS: Pell identities/positivity for indices 0 through 300.")
    print("PASS: modular return and exact divisibility for m=1 through 500.")
    print(f"      Largest first return index: {max_return[0]} "
          f"(mod {max_return[1]}).")

    # One common ordinary Pell coordinate works for the listed samples.
    u, v = pell(6)
    assert (u, v) == (19601, 13860)
    tr = root_mod(v)
    sr = P(tr) // v
    for x in range(-6, 7):
        if x == 0:
            witnesses = (0, 0, 0, 0, 0)
        else:
            assert v % x == 0
            witnesses = (u, v, v // x, sr, tr)
        uu, vv, ww, ss, tt = witnesses
        assert x * (uu * uu - 2 * vv * vv - 1) == 0
        assert x * (vv - x * ww) == 0
        assert x * (vv * ss - P(tt)) == 0
    print("PASS: Phi witnesses for all ordinary integers -6 through 6.")

    gaussians = [(1, 1), (2, 1), (3, 1), (2, 0), (-1, 1), (0, 1)]
    for ga in gaussians:
        aa, bb = ga
        norm = aa * aa + bb * bb
        assert (v * aa) % norm == 0 and (v * bb) % norm == 0
        w = (v * aa // norm, -v * bb // norm)
        assert gmul(ga, w) == (v, 0)
        assert u * u - 2 * v * v == 1 and v * sr == P(tr)
    assert gmul((1, 1), (1, -1)) == (2, 0)
    assert 2 * -21120 == P(1)
    print("PASS: six Gaussian Phi samples and the displayed 1+i witness.")

    for x in range(-100, 101):
        uu, vv = 1, 0
        while uu < abs(x):
            uu, vv = 3 * uu + 4 * vv, 2 * uu + 3 * vv
        squares = four_squares(uu * uu - x * x)
        F = (uu * uu - 2 * vv * vv - 1) ** 2
        F += (uu * uu - x * x - sum(z * z for z in squares)) ** 2
        assert F == 0
    print("PASS: exact quartic witnesses for all integers -100 through 100.")

    variables = [Poly.variable(j, nvars=8) for j in range(1, 8)]
    xx, uu, vv, a1, a2, a3, a4 = variables
    F4 = (uu ** 2 - 2 * vv ** 2 - 1) ** 2
    F4 += (uu ** 2 - xx ** 2 - a1 ** 2 - a2 ** 2 - a3 ** 2 - a4 ** 2) ** 2
    assert max(sum(e) for e in F4.terms) == 4
    print("PASS: expanded F4 has total degree exactly four.")

    ii = Poly.variable(0, radicand=-1)
    xx = Poly.variable(1, radicand=-1)
    gaussian_second_term = 1 - xx ** 2 - (ii * xx) ** 2 - 1
    assert gaussian_second_term == 0
    print("PASS: quartic collapse in the Gaussian ring, with a1=i*x, a2=1.")
    print("\nALL CHECKS PASSED.")
    print("Unverified by this program: general Hahn support theorems, the")
    print("all-moduli proof, number-field prime existence, all quantified")
    print("definability claims, and the proper-class interpretation.")


if __name__ == "__main__":
    main()
