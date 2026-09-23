#!/usr/bin/env python3
"""Exact finite checks for A Single Dilation Recovers Hahn Support.

Uses only the Python standard library. These checks verify finite identities,
not Hahn summability, infinite theorems, first-order semantics, or Lean proofs.
Run: python3 verify.py
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Callable

Exponent = tuple[F, ...]
Polynomial = dict[Exponent, F]
Form = dict[int, F]  # exterior-basis bitmask -> coefficient
COUNTS: dict[str, int] = {}


def check(name: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise AssertionError(f"{name}\nactual={actual!r}\nexpected={expected!r}")
    COUNTS[name] = COUNTS.get(name, 0) + 1


def clean(a: dict) -> dict:
    return {g: c for g, c in a.items() if c}


def add(a: dict, b: dict) -> dict:
    out = dict(a)
    for g, c in b.items():
        out[g] = out.get(g, F(0)) + c
    return clean(out)


def scale(c: F, a: dict) -> dict:
    return clean({g: c * b for g, b in a.items()})


@dataclass(frozen=True)
class MonomialAutomorphism:
    theta: Callable[[Exponent], Exponent]
    inverse_theta: Callable[[Exponent], Exponent]
    character: Callable[[Exponent], F]

    def apply(self, f: Polynomial, inverse: bool = False) -> Polynomial:
        out: Polynomial = {}
        for g, c in f.items():
            if inverse:
                h = self.inverse_theta(g)
                multiplier = 1 / self.character(h)
            else:
                h = self.theta(g)
                multiplier = self.character(g)
            out[h] = out.get(h, F(0)) + multiplier * c
        return clean(out)

    def iterate(self, f: Polynomial, n: int) -> Polynomial:
        for _ in range(abs(n)):
            f = self.apply(f, inverse=n < 0)
        return f


def difference(auto: MonomialAutomorphism, f: Polynomial, lam: F) -> Polynomial:
    return add(auto.apply(f), scale(-lam, f))


def partial_resolvent(auto: MonomialAutomorphism, f: Polynomial,
                      lam: F, n: int, forward: bool) -> Polynomial:
    out: Polynomial = {}
    if forward:
        for j in range(n):
            out = add(out, scale(-lam ** (-j - 1), auto.iterate(f, j)))
    else:
        for j in range(1, n + 1):
            out = add(out, scale(lam ** (j - 1), auto.iterate(f, -j)))
    return out


def sign_character(g: Exponent) -> F:
    if g[1].denominator != 1:
        raise ValueError("The finite sign-character tests use integral coordinates.")
    return F(-1 if int(g[1]) % 2 else 1)


def check_resolvents() -> None:
    dilation = MonomialAutomorphism(lambda g: (2*g[0],),
                                    lambda g: (g[0]/2,), lambda g: F(1))
    shear = MonomialAutomorphism(lambda g: (g[0], g[1]+g[0]),
                                lambda g: (g[0], g[1]-g[0]), sign_character)
    examples = [
        (dilation, {(F(1),): F(3), (F(2),): F(-5), (F(7, 2),): F(2)}, True),
        (dilation, {(F(-1),): F(3), (F(-2),): F(-5), (F(-7, 2),): F(2)}, False),
        (shear, {(F(1), F(-2)): F(3), (F(1), F(0)): F(-2),
                 (F(3), F(1)): F(7)}, True),
        (shear, {(F(-1), F(-2)): F(3), (F(-1), F(0)): F(-2),
                 (F(-3), F(1)): F(7)}, False),
    ]
    for auto, f, forward in examples:
        for lam in map(F, [-3, -1, 1, 2, F(5, 2)]):
            for n in range(1, 11):
                q = partial_resolvent(auto, f, lam, n, forward)
                endpoint = (scale(lam**(-n), auto.iterate(f, n)) if forward
                            else scale(lam**n, auto.iterate(f, -n)))
                check("orbit telescope", difference(auto, q, lam),
                      add(f, scale(F(-1), endpoint)))
                check("automorphism inverse", auto.apply(auto.apply(f), True), f)
                check("partial inverse valuation bound", min(q) >= min(f), True)
    f = {(F(0), F(j)): F(j + 4) for j in range(-3, 4)}
    for lam in map(F, [-1, 1, 2, -3]):
        p = {g: c for g, c in f.items() if shear.character(g) == lam}
        q = {g: c/(shear.character(g)-lam) for g, c in f.items()
             if shear.character(g) != lam}
        check("neutral inverse", difference(shear, q, lam), add(f, scale(F(-1), p)))
        check("neutral projection kills image", {g: c for g, c in
              difference(shear, f, lam).items() if shear.character(g) == lam}, {})


def exterior_operator(f: Form, j: int, wedge: bool) -> Form:
    out: Form = {}
    for mask, c in f.items():
        occupied = bool(mask & (1 << j))
        if occupied == wedge:
            continue
        sign = F(-1 if (mask & ((1 << j)-1)).bit_count() % 2 else 1)
        target = mask ^ (1 << j)
        out[target] = out.get(target, F(0)) + sign*c
    return clean(out)


def check_koszul() -> None:
    for d in range(1, 6):
        for values in product(map(F, [0, 1, -2]), repeat=d):
            proj = [F(v == 0) for v in values]
            inv = [1/v if v else F(0) for v in values]
            prefixes = [F(1)]
            for p in proj:
                prefixes.append(prefixes[-1]*p)

            def differential(f: Form) -> Form:
                result: Form = {}
                for j in range(d):
                    result = add(result, scale(values[j], exterior_operator(f, j, True)))
                return result

            def homotopy(f: Form) -> Form:
                result: Form = {}
                for j in range(d):
                    result = add(result, scale(inv[j]*prefixes[j],
                                               exterior_operator(f, j, False)))
                return result

            for mask in range(1 << d):
                e = {mask: F(1)}
                p_e = scale(prefixes[-1], e)
                check("Koszul dH+Hd", add(differential(homotopy(e)),
                       homotopy(differential(e))), add(e, scale(F(-1), p_e)))
                check("Koszul d squared", differential(differential(e)), {})
                check("Koszul H squared", homotopy(homotopy(e)), {})
                check("Koszul HP", homotopy(p_e), {})
                check("Koszul PH", scale(prefixes[-1], homotopy(e)), {})
                check("Koszul dP", differential(p_e), {})
                check("Koszul Pd", scale(prefixes[-1], differential(e)), {})


def multiply_truncated(a: list[F], b: list[F], n: int) -> list[F]:
    out = [F(0)]*(n+1)
    for i, c in enumerate(a):
        for j, e in enumerate(b):
            if i+j <= n:
                out[i+j] += c*e
    return out


def check_product_and_characters() -> None:
    n = 80
    y = [F(1)] + [F(0)]*n
    step = 1
    while step <= n:
        factor = [F(int(j % step == 0)) for j in range(n+1)]
        y = multiply_truncated(y, factor, n)
        step *= 2
    dy = [y[j//2] if j % 2 == 0 else F(0) for j in range(n+1)]
    right = multiply_truncated(y, [F(1), F(-1)], n)
    for j in range(n+1):
        check("Mahler product coefficient", dy[j], right[j])
    # On integral monomials, a sign character is a nontrivial twist.
    # D2 after the twist has coefficient -1; twist after D2 has coefficient +1.
    # This is a restriction of the complex phase twist exp(pi*i*g).
    # Only the integral exponents 1 and 2 are touched, so rational
    # coefficients suffice for this exact witness.
    twist = MonomialAutomorphism(lambda g: g, lambda g: g,
                                  lambda g: F(-1 if int(g[0]) % 2 else 1))
    doubling = MonomialAutomorphism(lambda g: (2*g[0],),
                                    lambda g: (g[0]/2,), lambda g: F(1))
    monomial = {(F(1),): F(1)}
    first = doubling.apply(twist.apply(monomial))
    second = twist.apply(doubling.apply(monomial))
    check("noncentralizing twist witness", (first, second),
          ({(F(2),): F(-1)}, {(F(2),): F(1)}))
    check("twist witness unequal", first != second, True)
    # An ordered additive exponent shear commutes with doubling.
    for a, b in product(range(-4, 5), repeat=2):
        shear_after_double = (2*a, 2*b+2*a)
        double_after_shear = (2*a, 2*(b+a))
        check("external lift commutes with doubling", shear_after_double, double_after_shear)
    # Exact quarter-period phase character on exponents in (1/4)Z:
    # represent Gaussian integers as pairs; projection is resonance g in Z.
    i_powers = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    for j in range(-24, 25):
        check("phase resonance", i_powers[j % 4] == (1, 0), F(j, 4).denominator == 1)


def main() -> None:
    check_resolvents()
    check_koszul()
    check_product_and_characters()
    print("A Single Dilation Recovers Hahn Support")
    print("Exact finite verification -- standard-library Python, rational arithmetic")
    print("=" * 73)
    for name, count in COUNTS.items():
        print(f"PASS  {name:<49} {count:>7}")
    print("-" * 73)
    print(f"TOTAL: {sum(COUNTS.values())} exact checks passed.")
    print("No tests failed.")
    print()
    print("Scope: finite telescopes including endpoint terms; finite diagonal Koszul")
    print("models in dimensions 1 through 5; initial Mahler product coefficients;")
    print("character and exponent identities. No infinite theorem, first-order")
    print("interpretation, proper-class statement, or Lean proof is certified.")


if __name__ == "__main__":
    main()
