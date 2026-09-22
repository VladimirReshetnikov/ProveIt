#!/usr/bin/env python3
"""Exact finite checks for 'Computable Surreal Numbers'.

Python 3.10+, standard library only. All arithmetic uses fractions.Fraction.
A power-series list stores coefficients of u**0, ..., u**(n-1), modulo u**n.
A Hahn dictionary is a *finite* rational-exponent polynomial, not an arbitrary
infinite surreal number. Finite halting-stage tables below are synthetic test
data; they do not decide actual unbounded halting. These checks supplement,
and cannot replace, the infinite proofs in the accompanying article.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial
from typing import Callable, Iterable, Mapping, Sequence
import unittest

Series = list[Q]
Hahn = dict[Q, Q]


def pad(a: Sequence[Q | int], n: int) -> Series:
    """Return a modulo u**n, padding with exact zeros."""
    if n < 0:
        raise ValueError("The truncation length must be nonnegative.")
    return [Q(a[k]) if k < len(a) else Q(0) for k in range(n)]


def add(a: Sequence[Q | int], b: Sequence[Q | int], n: int) -> Series:
    aa, bb = pad(a, n), pad(b, n)
    return [x + y for x, y in zip(aa, bb)]


def mul(a: Sequence[Q | int], b: Sequence[Q | int], n: int) -> Series:
    aa, bb = pad(a, n), pad(b, n)
    return [sum((aa[j] * bb[k-j] for j in range(k+1)), Q(0))
            for k in range(n)]


def power(a: Sequence[Q | int], exponent: int, n: int) -> Series:
    if exponent < 0:
        raise ValueError("Use inverse() before taking a negative power.")
    result = pad([1], n)
    base = pad(a, n)
    while exponent:
        if exponent & 1:
            result = mul(result, base, n)
        exponent >>= 1
        if exponent:
            base = mul(base, base, n)
    return result


def inverse(a: Sequence[Q | int], n: int) -> Series:
    """Reciprocal modulo u**n, with the supplied nonzero constant certificate."""
    aa = pad(a, n)
    if not n:
        return []
    if not aa[0]:
        raise ValueError("A nonzero constant coefficient is required.")
    result = [1 / aa[0]]
    for k in range(1, n):
        result.append(-sum((aa[j] * result[k-j] for j in range(1, k+1)),
                           Q(0)) / aa[0])
    return result


def derivative(a: Sequence[Q | int], n: int) -> Series:
    return [Q(k+1) * (Q(a[k+1]) if k+1 < len(a) else Q(0))
            for k in range(n)]


def integral(a: Sequence[Q | int], n: int) -> Series:
    if n < 0:
        raise ValueError("The truncation length must be nonnegative.")
    return ([Q(0)] + [Q(a[k-1])/k if k-1 < len(a) else Q(0)
                      for k in range(1, n)]) if n else []


def exponential(a: Sequence[Q | int], n: int) -> Series:
    """Formal exp(a), with a[0] == 0, using (exp a)' = a' exp a."""
    aa = pad(a, n)
    if not n:
        return []
    if aa[0]:
        raise ValueError("The formal input must have zero constant term.")
    result = [Q(1)]
    for k in range(1, n):
        result.append(sum((j * aa[j] * result[k-j] for j in range(1, k+1)),
                          Q(0)) / k)
    return result


def logarithm(a: Sequence[Q | int], n: int) -> Series:
    """Formal log(a), normalized by a[0] == 1 and log(a)[0] == 0."""
    aa = pad(a, n)
    if not n:
        return []
    if aa[0] != 1:
        raise ValueError("The formal input must have constant term one.")
    return integral(mul(derivative(aa, n-1), inverse(aa, n-1), n-1), n)


def compose(f: Sequence[Q | int], h: Sequence[Q | int], n: int) -> Series:
    """Finite coefficient evaluation of f(h) when h has zero constant term."""
    hh = pad(h, n)
    if n and hh[0]:
        raise ValueError("The inner series must have zero constant term.")
    out = pad([], n)
    for c in reversed(pad(f, n)):
        out = mul(out, hh, n)
        if n:
            out[0] += c
    return out


def polynomial_value(coefficients: Sequence[Sequence[Q | int]],
                     y: Sequence[Q | int], n: int) -> Series:
    """Evaluate sum_j coefficients[j](u) * y(u)**j modulo u**n."""
    out = pad([], n)
    for coefficient in reversed(coefficients):
        out = add(mul(out, y, n), coefficient, n)
    return out


def hensel(coefficients: Sequence[Sequence[Q | int]],
           residue_root: Q | int, n: int) -> Series:
    """Unique simple Hensel lift of a specified rational residue root.

    This routine needs the exact simple-root certificate at u=0. It is not
    an algorithm selecting a branch from arbitrary raw Puiseux names.
    """
    if n < 1:
        raise ValueError("At least one coefficient is required.")
    a = Q(residue_root)
    constants = [Q(c[0]) if c else Q(0) for c in coefficients]
    value = sum((c * a**j for j, c in enumerate(constants)), Q(0))
    slope = sum((j * constants[j] * a**(j-1)
                 for j in range(1, len(constants))), Q(0))
    if value or not slope:
        raise ValueError("The specified residue root must exist and be simple.")
    out = [a]
    for k in range(1, n):
        residual = polynomial_value(coefficients, out, k+1)[k]
        out.append(-residual / slope)
    return out


def binomial_coefficients(a: Q | int, n: int) -> Series:
    if n < 0:
        raise ValueError("The truncation length must be nonnegative.")
    result: Series = []
    current = Q(1)
    for k in range(n):
        result.append(current)
        current *= (Q(a) - k) / (k+1)
    return result


def clean(a: Mapping[Q | int, Q | int]) -> Hahn:
    return {Q(exponent): Q(coefficient) for exponent, coefficient in a.items()
            if coefficient}


def hahn_add(*inputs: Mapping[Q | int, Q | int]) -> Hahn:
    out: Hahn = {}
    for a in inputs:
        for q, c in a.items():
            qq = Q(q)
            out[qq] = out.get(qq, Q(0)) + Q(c)
    return clean(out)


def hahn_mul(a: Mapping[Q | int, Q | int],
             b: Mapping[Q | int, Q | int]) -> Hahn:
    out: Hahn = {}
    for q, x in a.items():
        for r, y in b.items():
            s = Q(q) + Q(r)
            out[s] = out.get(s, Q(0)) + Q(x) * Q(y)
    return clean(out)


def hahn_derivative(a: Mapping[Q | int, Q | int]) -> Hahn:
    return clean({Q(q)-1: Q(q)*Q(c) for q, c in a.items()})


def hahn_primitive_without_residue(a: Mapping[Q | int, Q | int]) -> Hahn:
    return clean({Q(q)+1: Q(c)/(Q(q)+1) for q, c in a.items() if Q(q) != -1})


def alpha(stage: int) -> Q:
    if stage < 0:
        raise ValueError("A stage must be nonnegative.")
    return 1 - Q(1, 2**(stage+1))


def reciprocal_power_of_two_stage(q: Q) -> int | None:
    """Decode q=2**(-stage-1), or report that it has no such form."""
    q = Q(q)
    d = q.denominator
    if q.numerator == 1 and d >= 2 and d & (d-1) == 0:
        return d.bit_length()-2
    return None


def coefficient_a(q: Q) -> int:
    return int(reciprocal_power_of_two_stage(1-Q(q)) is not None)


def coefficient_b(q: Q, halts_exactly: Callable[[int, int], bool]) -> int:
    """Coefficient decision using only one bounded exact-stage predicate."""
    q = Q(q)
    integer = q.numerator // q.denominator
    if integer < 1 or integer % 2 == 0:
        return 0
    stage = reciprocal_power_of_two_stage(q-integer)
    if stage is None:
        return 0
    return int(halts_exactly((integer-1)//2, stage))


class ExactChecks(unittest.TestCase):
    def test_01_inverse_recurrence(self) -> None:
        for a in ([2, 3, -1, 4], [1, 0, 0, -5], [Q(2, 3), Q(-7, 5)]):
            self.assertEqual(mul(a, inverse(a, 18), 18), pad([1], 18))

    def test_02_geometric_series(self) -> None:
        self.assertEqual(inverse([1, -1], 20), [Q(1)]*20)

    def test_03_exponential_factorials(self) -> None:
        self.assertEqual(exponential([0, 1], 18),
                         [Q(1, factorial(k)) for k in range(18)])

    def test_04_exponential_addition(self) -> None:
        n = 16
        a, b = [0, 1, 3, Q(2, 3)], [0, -2, 0, 1, 5]
        self.assertEqual(exponential(add(a, b, n), n),
                         mul(exponential(a, n), exponential(b, n), n))

    def test_05_log_exp_inverse(self) -> None:
        n = 16
        a = [0, 2, -1, Q(3, 7), 0, 4]
        self.assertEqual(logarithm(exponential(a, n), n), pad(a, n))

    def test_06_exp_log_inverse(self) -> None:
        n = 16
        a = [1, 2, -1, Q(3, 7), 0, 4]
        self.assertEqual(exponential(logarithm(a, n), n), pad(a, n))

    def test_07_formal_composition(self) -> None:
        n = 14
        h = [0, 0, 2, 1]
        f = [Q(1, factorial(k)) for k in range(n)]
        self.assertEqual(compose(f, h, n), exponential(h, n))

    def test_08_hensel_quadratic(self) -> None:
        n = 18
        polynomial = [[-1, -1], [], [1]]  # Y^2 - (1+u)
        y = hensel(polynomial, 1, n)
        self.assertEqual(y, binomial_coefficients(Q(1, 2), n))
        self.assertEqual(polynomial_value(polynomial, y, n), pad([], n))

    def test_09_hensel_cubic(self) -> None:
        n = 18
        polynomial = [[-1, -1, 0, -2], [], [], [1]]
        y = hensel(polynomial, 1, n)
        self.assertEqual(polynomial_value(polynomial, y, n), pad([], n))

    def test_10_finite_prefix_regularization(self) -> None:
        n = 18
        # F(Y)=Y^2-u^2(1+u), p=u, N=2, d=1.
        # H(W)=u^(-3) F(u+u^2 W)=2W-1+u W^2.
        w = hensel([[-1], [2], [0, 1]], Q(1, 2), n-2)
        z = [Q(0), Q(1)] + w
        self.assertEqual(polynomial_value([[0, 0, -1, -1], [], [1]], z, n),
                         pad([], n))
        self.assertEqual(z, [Q(0)] + binomial_coefficients(Q(1, 2), n-1))

    def test_11_ramified_quadratic(self) -> None:
        n = 12
        b = binomial_coefficients(Q(1, 2), n)
        y = {Q(3, 2)+k: c for k, c in enumerate(b)}
        square = hahn_mul(y, y)
        observed = {q: c for q, c in square.items() if q < 3+n}
        self.assertEqual(observed, {Q(3): Q(1), Q(4): Q(1)})
        self.assertEqual(b[:5], [Q(1), Q(1, 2), Q(-1, 8), Q(1, 16), Q(-5, 128)])

    def test_12_differential_homotopies(self) -> None:
        f = {Q(-3, 2): Q(7), Q(-1): Q(3), Q(0): Q(-2), Q(5, 3): Q(11)}
        dj = hahn_derivative(hahn_primitive_without_residue(f))
        jd = hahn_primitive_without_residue(hahn_derivative(f))
        self.assertEqual(dj, hahn_add(f, {Q(-1): Q(-3)}))
        self.assertEqual(jd, hahn_add(f, {Q(0): Q(2)}))

    def test_13_leibniz_rule_on_ramified_terms(self) -> None:
        f, g = {Q(-2, 3): 2, Q(1, 2): -1}, {Q(-1): 3, Q(5, 7): 4}
        self.assertEqual(hahn_derivative(hahn_mul(f, g)),
                         hahn_add(hahn_mul(hahn_derivative(f), g),
                                  hahn_mul(f, hahn_derivative(g))))

    def test_14_support_deciders(self) -> None:
        stages = {0: 2, 3: 5, 5: 0, 8: 31}
        predicate = lambda e, s: stages.get(e) == s
        for s in range(50):
            self.assertEqual(coefficient_a(alpha(s)), 1)
        for e in range(12):
            for s in range(40):
                q = 2*e+2-alpha(s)
                self.assertEqual(coefficient_b(q, predicate), int(stages.get(e) == s))
        for q in (Q(0), Q(1), Q(-1), Q(1, 3), Q(6, 5)):
            self.assertEqual(coefficient_a(q), 0)
        for q in (Q(0), Q(1), Q(-1), Q(4, 3), Q(5, 3), Q(7, 2)):
            self.assertEqual(coefficient_b(q, predicate), 0)

    def test_15_halting_exponent_collision(self) -> None:
        stages = {0: 2, 2: 5, 3: 0, 5: 31, 8: 8, 13: 4}
        a = {alpha(s): Q(1) for s in range(33)}
        b = {2*e+2-alpha(s): Q(1) for e, s in stages.items()}
        product = hahn_mul(a, b)
        for e in range(20):
            self.assertEqual(product.get(Q(2*e+2), Q(0)), Q(int(e in stages)))
        for e, s in stages.items():
            collisions = [(k, other) for k in range(33) for other in stages
                          if alpha(k)+2*other+2-alpha(stages[other]) == 2*e+2]
            self.assertEqual(collisions, [(s, e)])

    def test_16_obstruction_coefficients(self) -> None:
        # Finite witnesses of the two expansions used in the oracle reductions.
        for a in (Q(1), Q(1, 2), Q(1, 1000)):
            self.assertEqual(inverse([a, 1], 9),
                             [(-1)**n / a**(n+1) for n in range(9)])
            root = hensel([[-a*a, 0, -1], [], [1]], a, 12)
            self.assertEqual(root[1], Q(0))
        self.assertEqual(hahn_mul({Q(-1): Q(1)}, {Q(1): Q(1)}), {Q(0): Q(1)})
        self.assertEqual(hahn_mul({Q(1): Q(1)}, {Q(1): Q(1)}), {Q(2): Q(1)})

    def test_17_positive_support_word_bound(self) -> None:
        n = 15
        h = [0, 0, 1, 2]
        for k in range(1, n):
            kth = power(h, k, n)
            self.assertTrue(all(c == 0 for c in kth[:min(2*k, n)]))
        geometric = pad([], n)
        for k in range(n):
            geometric = add(geometric, power(h, k, n), n)
        one_minus_h = add([1], [-Q(c) for c in h], n)
        self.assertEqual(mul(one_minus_h, geometric, n), pad([1], n))

    def test_18_input_contracts(self) -> None:
        with self.assertRaises(ValueError):
            inverse([0, 1], 5)
        with self.assertRaises(ValueError):
            exponential([1], 5)
        with self.assertRaises(ValueError):
            logarithm([2], 5)
        with self.assertRaises(ValueError):
            hensel([[], [], [1]], 0, 5)  # Repeated residue root.
        with self.assertRaises(ValueError):
            compose([1, 2], [1], 5)
        with self.assertRaises(ValueError):
            alpha(-1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
