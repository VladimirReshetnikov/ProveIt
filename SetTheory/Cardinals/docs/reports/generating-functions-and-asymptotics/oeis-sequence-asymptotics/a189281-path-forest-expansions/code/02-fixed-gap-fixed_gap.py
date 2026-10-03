#!/usr/bin/env python3
"""Recurrence-free enumeration and asymptotic coefficients for fixed-gap permutations.

The exact enumerator is a direct path-tiling inclusion--exclusion calculation.
The coefficient engine implements the finite-defect theorem in article.tex.
Neither computation uses a guessed recurrence. All symbolic arithmetic is exact.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from functools import lru_cache
from math import comb, factorial, prod
from typing import Iterator, Mapping, Sequence
import sympy as sp

HVAR = sp.Symbol("h")
Profile = tuple[int, ...]  # Sorted non-singleton tile sizes.


def long_profiles(defect: int, size: int = 3) -> Iterator[dict[int, int]]:
    """Enumerate m_j (j>=3) with sum((j-2)*m_j) == defect."""
    if defect < 0:
        raise ValueError("Defect must be nonnegative")
    if defect == 0:
        yield {}
        return
    if size - 2 > defect:
        return
    for multiplicity in range(defect // (size - 2) + 1):
        rest = defect - (size - 2) * multiplicity
        for profile in long_profiles(rest, size + 1):
            yield ({size: multiplicity, **profile} if multiplicity else profile)


def series_product(a: Sequence[sp.Expr], b: Sequence[sp.Expr], order: int
                   ) -> list[sp.Expr]:
    """Multiply two ordinary formal series through the specified order."""
    return [sp.expand(sum(a[i] * b[j-i]
                         for i in range(max(0, j-len(b)+1), min(j, len(a)-1)+1)))
            for j in range(order+1)]


@lru_cache(None)
def binomial_h(order: int) -> sp.Expr:
    return sp.prod(HVAR-i for i in range(order)) / sp.factorial(order)


@lru_cache(None)
def power_sum(order: int) -> sp.Poly:
    """F_q(x)=sum(i**q, i=0,...,x-1), as an exact polynomial."""
    x = sp.Symbol("x")
    return sp.Poly((sp.bernoulli(order+1, x)-sp.bernoulli(order+1, 0))
                   / (order+1), x)


def profile_kernel(profile: Mapping[int, int], order: int,
                   r: sp.Expr | int, s: sp.Expr | int) -> list[sp.Expr]:
    """Coefficients of B(t;k,c) U_r(t) U_s(t), with h free dimers."""
    r, s = sp.sympify(r), sp.sympify(s)
    k0 = sum((j-1)*m for j, m in profile.items())
    c0 = sum(profile.values())
    k, c = HVAR+k0, HVAR+c0
    logarithm = [sp.Integer(0)] + [
        sp.expand(-(power_sum(q).eval(k+c)-2*power_sum(q).eval(k))/q)
        for q in range(1, order+1)]
    base = [sp.Integer(1)]
    for j in range(1, order+1):
        base.append(sp.expand(sum(q*logarithm[q]*base[j-q]
                                  for q in range(1, j+1))/j))

    z = sp.Symbol("z")
    fixed = sp.Poly(sp.prod((1+(j-1)*z)**m for j, m in profile.items()), z)
    elementary = [sp.expand(sum(fixed.nth(i)*binomial_h(ell-i)
                               for i in range(min(ell, fixed.degree())+1)))
                  for ell in range(order+1)]
    boundary: dict[sp.Expr, list[sp.Expr]] = {}
    for count in {r, s}:
        result = [sp.Integer(0)]*(order+1)
        for ell in range(order+1):
            factor = (-1)**ell * sp.rf(count-1, ell) * elementary[ell]
            if factor == 0:
                continue
            denominator = [sp.Integer(1)] + [sp.Integer(0)]*(order-ell)
            for i in range(ell):
                denominator = series_product(
                    denominator, [(k+i)**a for a in range(order-ell+1)],
                    order-ell)
            for a in range(order-ell+1):
                result[a+ell] += factor*denominator[a]
        boundary[count] = [sp.expand(x) for x in result]
    return series_product(series_product(base, boundary[r], order),
                          boundary[s], order)


@lru_cache(None)
def touchard(order: int, parameter: sp.Expr) -> sp.Expr:
    """T_q(parameter), using its polynomial recurrence."""
    if order == 0:
        return sp.Integer(1)
    x = sp.Symbol("_poisson_parameter")
    # Compute once with a genuine symbol; substituting first is not differentiable.
    return sp.expand(touchard_symbolic(order).subs(x, parameter))


@lru_cache(None)
def touchard_symbolic(order: int) -> sp.Expr:
    x = sp.Symbol("_poisson_parameter")
    if order == 0:
        return sp.Integer(1)
    previous = touchard_symbolic(order-1)
    return sp.expand(x*(previous+sp.diff(previous, x)))


def poisson_transform(polynomial: sp.Expr, parameter: sp.Expr) -> sp.Expr:
    p = sp.Poly(polynomial, HVAR)
    return sp.expand(sum(coefficient*touchard(power[0], parameter)
                         for power, coefficient in p.terms()))


def asymptotic_coefficients(order: int, r: sp.Expr | int, s: sp.Expr | int,
                            eta: sp.Expr | int = 1, z: sp.Expr | int = -1
                            ) -> list[sp.Expr]:
    """Return C_0,...,C_order in G_n(1+z) ~ exp(eta*z)*sum C_j/n**j.

    eta=1: directed differences; eta=2: absolute differences. Symbolic eta
    is also supported as a formal component weight. z=-1 gives avoidance.
    """
    if not isinstance(order, int) or order < 0:
        raise ValueError("Order must be a nonnegative integer")
    eta, z = sp.sympify(eta), sp.sympify(z)
    answer = [sp.Integer(0)]*(order+1)
    for defect in range(order+1):
        for profile in long_profiles(defect):
            kernel = profile_kernel(profile, order-defect, r, s)
            k0 = sum((j-1)*m for j, m in profile.items())
            c0 = sum(profile.values())
            factor = eta**c0*z**k0/sp.prod(sp.factorial(m)
                                          for m in profile.values())
            for j, polynomial in enumerate(kernel):
                answer[defect+j] += factor*poisson_transform(polynomial, eta*z)
    return [sp.factor(a) for a in answer]


def gap_lengths(n: int, gap: int) -> tuple[int, ...]:
    if n < 0 or gap < 1:
        raise ValueError("Require n>=0 and gap>=1")
    return tuple((n-1-i)//gap+1 for i in range(min(n, gap)))


@lru_cache(None)
def path_profiles(length: int) -> dict[Profile, int]:
    """Exact tilings of a path; singleton tiles are suppressed in the key."""
    if length < 0:
        raise ValueError("Length must be nonnegative")
    if length == 0:
        return {(): 1}
    answer: defaultdict[Profile, int] = defaultdict(int, path_profiles(length-1))
    for tile in range(2, length+1):
        for profile, count in path_profiles(length-tile).items():
            answer[tuple(sorted((*profile, tile)))] += count
    return dict(answer)


@lru_cache(None)
def forest_profiles(lengths: tuple[int, ...]) -> dict[Profile, int]:
    if any(length < 1 for length in lengths):
        raise ValueError("Nonempty paths must have positive lengths")
    answer = {(): 1}
    for length in lengths:
        product: defaultdict[Profile, int] = defaultdict(int)
        for a, acount in answer.items():
            for b, bcount in path_profiles(length).items():
                product[tuple(sorted(a+b))] += acount*bcount
        answer = dict(product)
    return answer


def moment_counts(rows: tuple[int, ...], values: tuple[int, ...], eta: int = 1
                  ) -> list[int]:
    """Return T_k=n! E[binom(X,k)] by exact tiling, without any recurrence."""
    if eta not in (1, 2) or sum(rows) != sum(values):
        raise ValueError("Require eta in {1,2} and equal total sizes")
    n = sum(rows)
    left, right = forest_profiles(rows), forest_profiles(values)
    answer = [0]*(n+1)
    for profile, a in left.items():
        b = right.get(profile, 0)
        if not b:
            continue
        v, c = sum(profile), len(profile)
        multiplicity = prod(factorial(m) for m in Counter(profile).values())
        answer[v-c] += a*b*factorial(n-v)*multiplicity*eta**c
    return answer


def avoidance(n: int, r: int, s: int, eta: int = 1) -> int:
    return sum((-1)**k*t for k, t in enumerate(
        moment_counts(gap_lengths(n, r), gap_lengths(n, s), eta)))


def histogram(rows: tuple[int, ...], values: tuple[int, ...], eta: int = 1
              ) -> list[int]:
    moments = moment_counts(rows, values, eta)
    return [sum((-1)**(k-j)*comb(k, j)*moments[k]
                for k in range(j, len(moments)))
            for j in range(len(moments))]


def falling(value: int, order: int) -> int:
    return prod(value-i for i in range(order))


def stable_profile_count(n: int, paths: int, profile: Profile) -> int:
    """The stable polynomial C_paths(n;profile); valid if min length >= k."""
    c, k = len(profile), sum(profile)-len(profile)
    elementary = [1]
    for j in profile:
        previous = elementary
        elementary = [0]*(len(previous)+1)
        for ell, value in enumerate(previous):
            elementary[ell] += value
            elementary[ell+1] += (j-1)*value
    numerator = 0
    for ell, value in enumerate(elementary):
        rising = prod(paths-1+i for i in range(ell))
        numerator += (-1)**ell*rising*value*falling(n-k-ell, c-ell)
    denominator = prod(factorial(m) for m in Counter(profile).values())
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError("Stable tiling expression did not give an integer")
    return quotient
