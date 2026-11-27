#!/usr/bin/env python3
"""Check the Laurent reconstruction in the accompanying paper using exact algebra.

Run with Python 3 and SymPy (tested with 1.14.0): python check_algebra.py
Coefficient lists are in descending powers of z. All test data are exact.
The checks concern the algebraic inverse, not the analytic estimate on zeros.
"""

from math import comb

import sympy as sp


def translate(coefficients, shift):
    """Coefficients of Q(z+shift) in the same ordering as Q."""
    degree = len(coefficients) - 1
    return [
        sp.expand(sum(coefficients[j] * comb(degree - j, k - j) * shift ** (k - j)
                      for j in range(k + 1)))
        for k in range(degree + 1)
    ]


def ratio_jet(coefficients, step, length):
    """Terms through z^(-length) of Q(z-step)/Q(z), for monic Q."""
    assert coefficients[0] == 1
    shifted = translate(coefficients, -step)
    degree = len(coefficients) - 1
    jet = [sp.Integer(1)]
    for k in range(1, length + 1):
        numerator = shifted[k] if k <= degree else 0
        correction = sum(coefficients[j] * jet[k - j]
                         for j in range(1, min(k, degree) + 1))
        jet.append(sp.expand(numerator - correction))
    return jet


def recover(jet, step):
    """Recover degree and monic polynomial from its exact finite ratio jet."""
    degree = sp.cancel(-jet[1] / step)
    if degree.is_Integer is not True or degree < 0:
        raise ValueError("the first coefficient does not encode a polynomial degree")
    degree = int(degree)
    if len(jet) < degree + 2:
        raise ValueError(f"degree {degree} needs terms through index {degree + 1}")
    coefficients = [sp.Integer(1)] + [sp.Integer(0)] * degree
    for j in range(1, degree + 1):
        baseline = ratio_jet(coefficients, step, j + 1)[j + 1]
        coefficients[j] = sp.cancel((jet[j + 1] - baseline) / (j * step))
    return coefficients


def require_equal(left, right):
    assert len(left) == len(right)
    for lvalue, rvalue in zip(left, right):
        assert sp.expand(lvalue - rvalue) == 0, (lvalue, rvalue)


def check_example():
    # Use the quadratic character modulo 5 with p=2. Divide the measured
    # prime coefficient by chi(2)=-1 before forming this ratio jet.
    # h=log(2) and c=log(5)/2 can be kept symbolic throughout.
    h, c = sp.symbols("h c", positive=True)
    source = [1, -sp.I, 2]  # (z-2i)(z+i)
    shifted = translate(source, c)
    jet = ratio_jet(shifted, h, 3)
    a, b = shifted[1:]
    require_equal(jet, [1, -2*h, h*h + a*h, (2*b-a*a)*h-a*h*h])
    restored = recover(jet, h)
    require_equal(restored, shifted)
    inferred_c = sp.simplify(sp.re(restored[1]) / 2)
    assert inferred_c == c
    require_equal(translate(restored, -inferred_c), source)
    print("q=5, p=2, P=(z-2i)(z+i), h=log(2), c=log(5)/2")
    for j, value in enumerate(jet):
        print(f"  coefficient of z^(-{j}): {sp.factor(value)}")
    print("  recovered shift and monic polynomial exactly")


def check_sharpness():
    x = sp.symbols("x", real=True)
    h = sp.Rational(7, 4)
    for d in range(1, 9):
        # At the endpoints of every disjoint interval [k-1/4,k+1/4],
        # f has opposite signs. A sufficiently small constant perturbation
        # preserves them, hence preserves d distinct real roots by the IVT.
        f = sp.Poly(sp.prod(x-j for j in range(1, d+1)), x)
        endpoints = [(j-sp.Rational(1, 4), j+sp.Rational(1, 4))
                     for j in range(1, d+1)]
        eps = min(abs(f.eval(t)) for pair in endpoints for t in pair) / 2
        for left, right in endpoints:
            assert (f.eval(left) + eps) * (f.eval(right) + eps) < 0
        # P(z)=i^d f(z/i) has imaginary roots. The second polynomial
        # comes from f+eps, so it stays in the permitted operator class.
        first = [sp.I**k * a for k, a in enumerate(f.all_coeffs())]
        second = first.copy()
        second[-1] += sp.I**d * eps
        first_jet = ratio_jet(first, h, d+1)
        second_jet = ratio_jet(second, h, d+1)
        require_equal(first_jet[:d+1], second_jet[:d+1])
        require_equal([second_jet[d+1] - first_jet[d+1]],
                      [d * h * (second[-1] - first[-1])])
        assert second_jet[d+1] != first_jet[d+1]
        require_equal(recover(first_jet, h), first)
        require_equal(recover(second_jet, h), second)
    print("matched jets through d and separated at d+1 for d=1,...,8")


if __name__ == "__main__":
    check_example()
    check_sharpness()
    require_equal(recover(ratio_jet([1], sp.Integer(2), 1), sp.Integer(2)), [1])
    print("all exact checks passed")
