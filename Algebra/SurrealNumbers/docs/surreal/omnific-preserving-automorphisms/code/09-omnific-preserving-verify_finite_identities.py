#!/usr/bin/env python3
"""Exact finite checks for Omnific-Preserving Automorphisms.

Python 3.10+, standard library only. These tests check finite algebraic
identities, not the general Hahn-support or class-theoretic theorems.
Run: python3 verify_finite_identities.py
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from random import Random
from typing import TypeAlias

Vector: TypeAlias = tuple[F, ...]
Polynomial: TypeAlias = dict[Vector, F]


def vector_add(x: Vector, y: Vector) -> Vector:
    if len(x) != len(y):
        raise ValueError("Vector dimensions differ")
    return tuple(a + b for a, b in zip(x, y))


def vector_scale(a: F, x: Vector) -> Vector:
    return tuple(a * b for b in x)


def dot(x: Vector, y: Vector) -> F:
    if len(x) != len(y):
        raise ValueError("Vector dimensions differ")
    return sum((a * b for a, b in zip(x, y)), F(0))


def basis(rank: int, index: int) -> Vector:
    """Coordinate index is one-based, as in the article."""
    if not 1 <= index <= rank:
        raise ValueError("Coordinate index out of range")
    return tuple(F(j == index) for j in range(1, rank + 1))


def positive(x: Vector) -> bool:
    """Reverse-lexicographic positivity (last nonzero coordinate wins)."""
    for value in reversed(x):
        if value:
            return value > 0
    return False


def clean(p: Polynomial) -> Polynomial:
    return {g: a for g, a in p.items() if a}


def poly_add(p: Polynomial, q: Polynomial, sign: F = F(1)) -> Polynomial:
    out = dict(p)
    for g, a in q.items():
        out[g] = out.get(g, F(0)) + sign * a
    return clean(out)


def poly_mul(p: Polynomial, q: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for g, a in p.items():
        for h, b in q.items():
            v = vector_add(g, h)
            out[v] = out.get(v, F(0)) + a * b
    return clean(out)


@dataclass(frozen=True)
class HomogeneousDerivation:
    shift: Vector
    functional: Vector

    def __post_init__(self) -> None:
        if len(self.shift) != len(self.functional):
            raise ValueError("Shift and functional dimensions differ")
        if not positive(self.shift):
            raise ValueError("Derivation shift must be positive")

    def apply(self, p: Polynomial) -> Polynomial:
        out: Polynomial = {}
        for g, a in p.items():
            coefficient = a * dot(self.functional, g)
            if coefficient:
                h = vector_add(g, self.shift)
                out[h] = out.get(h, F(0)) + coefficient
        return clean(out)

    def bracket(self, other: HomogeneousDerivation) -> HomogeneousDerivation:
        # [D_delta,theta, D_epsilon,psi]
        # = D_delta+epsilon, theta(epsilon)*psi - psi(delta)*theta.
        a = dot(self.functional, other.shift)
        b = dot(other.functional, self.shift)
        functional = vector_add(
            vector_scale(a, other.functional),
            vector_scale(-b, self.functional),
        )
        return HomogeneousDerivation(vector_add(self.shift, other.shift), functional)


def random_poly(rank: int, rng: Random, terms: int = 4) -> Polynomial:
    out: Polynomial = {}
    for _ in range(terms):
        g = tuple(F(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(rank))
        a = F(rng.randint(-5, 5), rng.randint(1, 4))
        out[g] = out.get(g, F(0)) + a
    return clean(out)


def a_vector(rank: int, k: int) -> Vector:
    return tuple(F(2 ** (k - h)) if h <= k else F(0)
                 for h in range(1, rank + 1))


def target_y(rank: int, k: int, j: int, i: int) -> HomogeneousDerivation:
    if not 0 <= k < j < i <= rank:
        raise ValueError("Indices must satisfy 0 <= k < j < i <= rank")
    return HomogeneousDerivation(
        vector_add(a_vector(rank, k), basis(rank, j)), basis(rank, i)
    )


def checked_balanced_y(rank: int, k: int, j: int, i: int) -> HomogeneousDerivation:
    expected = target_y(rank, k, j, i)
    if k == 0:
        return expected
    left = checked_balanced_y(rank, k - 1, k, j)
    right = checked_balanced_y(rank, k - 1, j, i)
    actual = left.bracket(right)
    assert actual == expected, (rank, k, j, i, actual, expected)
    return actual


# A tree is a leaf derivation or a pair of trees. Each occurrence is fresh.
Tree: TypeAlias = HomogeneousDerivation | tuple['Tree', 'Tree']


def balanced_tree(rank: int, k: int, j: int, i: int) -> Tree:
    if k == 0:
        return target_y(rank, 0, j, i)
    return (balanced_tree(rank, k - 1, k, j),
            balanced_tree(rank, k - 1, j, i))


def mixed_group_coefficient(tree: Tree, seed: Vector) -> tuple[F, Vector, int]:
    """Evaluate a group word over Q[s_1,...,s_m]/(s_1^2,...,s_m^2).

    Each exp(s_j D_j) is exactly 1+s_j D_j in this quotient. The mask
    records which parameters are present. For a given mask, the output
    exponent is the seed plus the sum of that mask's leaf shifts.
    """
    leaves: list[HomogeneousDerivation] = []

    def invert(word: list[tuple[int, int]]) -> list[tuple[int, int]]:
        return [(index, -sign) for index, sign in reversed(word)]

    def make_word(node: Tree) -> list[tuple[int, int]]:
        if isinstance(node, HomogeneousDerivation):
            index = len(leaves)
            leaves.append(node)
            return [(index, 1)]
        left, right = make_word(node[0]), make_word(node[1])
        return left + right + invert(left) + invert(right)

    word = make_word(tree)

    @lru_cache(maxsize=None)
    def exponent(mask: int) -> Vector:
        if mask == 0:
            return seed
        bit = mask & -mask
        index = bit.bit_length() - 1
        return vector_add(exponent(mask ^ bit), leaves[index].shift)

    state: dict[int, F] = {0: F(1)}
    # Composition acts on the input from right to left.
    for index, sign in reversed(word):
        bit = 1 << index
        out = dict(state)
        for mask, coefficient in state.items():
            if not mask & bit:
                contribution = sign * coefficient * dot(
                    leaves[index].functional, exponent(mask)
                )
                new_mask = mask | bit
                out[new_mask] = out.get(new_mask, F(0)) + contribution
        state = {mask: a for mask, a in out.items() if a}
    full_mask = (1 << len(leaves)) - 1
    return state.get(full_mask, F(0)), exponent(full_mask), len(leaves)


def run() -> None:
    rng = Random(20260923)
    print("Omnific-Preserving Automorphisms: exact finite verification")
    print("All coefficients below use fractions.Fraction.\n")

    for case in range(240):
        rank = 2 + case % 4
        delta = vector_scale(F(rng.randint(1, 3)), basis(rank, rng.randint(1, rank)))
        epsilon = vector_scale(F(rng.randint(1, 3)), basis(rank, rng.randint(1, rank)))
        theta = tuple(F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(rank))
        psi = tuple(F(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(rank))
        d = HomogeneousDerivation(delta, theta)
        e = HomogeneousDerivation(epsilon, psi)
        p, q = random_poly(rank, rng), random_poly(rank, rng)
        assert d.apply(poly_mul(p, q)) == poly_add(
            poly_mul(d.apply(p), q), poly_mul(p, d.apply(q)))
        assert poly_add(d.apply(e.apply(p)), e.apply(d.apply(p)), F(-1)) == d.bracket(e).apply(p)
    print("PASS: 240 rational finite-polynomial product-rule and bracket tests")

    recursion_count = 0
    for rank in range(2, 9):
        for k in range(rank - 1):
            for j in range(k + 1, rank):
                for i in range(j + 1, rank + 1):
                    checked_balanced_y(rank, k, j, i)
                    recursion_count += 1
    print(f"PASS: {recursion_count} balanced derived-series recursions (ranks 2 through 8)")

    for rank in range(2, 6):
        k, j, i = rank - 2, rank - 1, rank
        seed = vector_scale(F(3, 2), basis(rank, i))
        coefficient, exponent, leaves = mixed_group_coefficient(
            balanced_tree(rank, k, j, i), seed)
        target = target_y(rank, k, j, i)
        assert coefficient == F(3, 2), (rank, coefficient)
        assert exponent == vector_add(seed, target.shift)
        print(f"PASS: rank {rank} mixed group-commutator coefficient = 3/2 ({leaves} independent parameters)")

    # Same-scale terms commute; a smaller/larger pair gives the larger scale.
    for rank in range(3, 9):
        for j in range(1, rank - 1):
            d = HomogeneousDerivation(basis(rank, j), basis(rank, j + 1))
            e = HomogeneousDerivation(vector_scale(F(2), basis(rank, j)), basis(rank, rank))
            assert not any(d.bracket(e).functional)
    print("PASS: same-convex-scale commutators vanish in coordinate models")

    d = HomogeneousDerivation(basis(3, 1), basis(3, 2))
    current = HomogeneousDerivation(basis(3, 2), basis(3, 3))
    for n in range(17):
        assert current == HomogeneousDerivation(
            vector_add(basis(3, 2), vector_scale(F(n), basis(3, 1))), basis(3, 3))
        current = d.bracket(current)
    print("PASS: 17 successive nonzero lower-central brackets in rank 3")

    shear = HomogeneousDerivation(basis(2, 1), basis(2, 2))
    seed = (F(-2), F(-3, 2))
    p: Polynomial = {seed: F(1)}
    for n in range(17):
        expected = {vector_add(seed, vector_scale(F(n), basis(2, 1))): F(-3, 2) ** n}
        assert p == expected
        p = shear.apply(p)
    print("PASS: homogeneous shear iterate formula through order 16")

    order = 14
    for _ in range(60):
        a, b = F(rng.randint(-6, 6), 3), F(rng.randint(-6, 6), 4)
        for n in range(order + 1):
            product = sum((a**j * b**(n-j) / (factorial(j) * factorial(n-j))
                           for j in range(n + 1)), F(0))
            assert product == (a+b)**n / factorial(n)
    print("PASS: 60 exponential addition specializations through order 14")

    gamma = F(-1, 2)
    rising = F(1)
    coefficients = [F(1)]
    for n in range(1, 9):
        rising *= gamma + n - 1
        coefficients.append(rising / factorial(n))
    assert coefficients[:5] == [F(1), F(-1, 2), F(-1, 8), F(-1, 16), F(-5, 128)]
    assert gamma + 1 > 0 and coefficients[1] != 0
    print("PASS: rank-one translation creates a nonzero positive-exponent term")

    u, v = 1, 0
    for m in range(31):
        assert u*u - 2*v*v == 1
        assert u >= 3**m
        u, v = 3*u + 4*v, 2*u + 3*v
    print("PASS: 31 Pell solutions and their elementary growth bound")
    print("\nALL CHECKS PASSED")
    print("Scope: finite identities only; no claim of full theorem or Lean verification.")


if __name__ == '__main__':
    run()
