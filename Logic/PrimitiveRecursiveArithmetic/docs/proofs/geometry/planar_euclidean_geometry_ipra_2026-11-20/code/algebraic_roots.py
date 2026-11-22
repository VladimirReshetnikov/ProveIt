"""Polynomial roots with exact real algebraic coefficients (optional SymPy).

Run the checks with python3 algebraic_roots.py using SymPy 1.14. Coefficients
are passed in ascending degree. The base exact_scalars module uses Python's
standard library only. SymPy accelerates the rational elimination, rational
factorization and certified isolation for this executable example.
"""
from fractions import Fraction as Q
from math import ceil

import sympy as sp

from exact_scalars import Scalar
from scalar_records import RootRecord, mesh, poly


def _rational(value):
    numerator, denominator = value.as_numer_denom()
    return Q(int(numerator), int(denominator))


def _poly_expr(coefficients, x):
    return sum(sp.Rational(c.numerator, c.denominator) * x**i
               for i, c in enumerate(coefficients))


def _rational_eliminant(monic, z):
    """Norm of the monic input, taking an independent generator per coefficient."""
    result = z ** (len(monic) - 1)
    constraints = []
    for degree, coefficient in enumerate(monic[:-1]):
        p = coefficient.record.p
        if len(p) == 2:
            a = -p[0] / p[1]
            term = sp.Rational(a.numerator, a.denominator)
        else:
            term = sp.Dummy(f"t{degree}")
            defining_poly = _poly_expr((q / p[-1] for q in p), term)
            constraints.append((defining_poly, term))
        result += term * z**degree
    for defining_poly, generator in constraints:
        result = sp.resultant(defining_poly, result, generator)
    result = sp.Poly(result, z, domain=sp.QQ)
    expected = len(monic) - 1
    for defining_poly, generator in constraints:
        expected *= sp.degree(defining_poly, generator)
    # Resultant routines may reorder the arguments, introducing a unit sign.
    # Preserve the monic norm and verify its degree against the free basis.
    if result.degree() != expected or abs(result.LC()) != 1:
        raise ArithmeticError("unexpected degree or leading coefficient in norm")
    return result.monic()


def _isolated_candidates(eliminant):
    for factor, _ in eliminant.factor_list()[1]:
        p = poly(_rational(c) for c in reversed(factor.monic().all_coeffs()))
        if len(p) == 2:
            yield Scalar.rational(-p[0] / p[1])
            continue
        radius = Q(5 + ceil(sum(abs(c) for c in p[:-1])))
        _, delta = mesh(p, radius)
        for (a, b), _ in factor.intervals(eps=sp.Rational(delta.numerator, delta.denominator)):
            left, right = _rational(a), _rational(b)
            if left == right:
                yield Scalar.rational(left)
            else:
                # The independent derivative and sign checks run in RootRecord.
                yield Scalar.from_record(RootRecord(p, left, right))


def roots_over_scalars(coefficients):
    """Return the distinct real roots in order; the zero polynomial raises."""
    coeffs = [value if isinstance(value, Scalar) else Scalar.rational(value)
              for value in coefficients]
    while coeffs and not coeffs[-1]:
        coeffs.pop()
    if not coeffs:
        raise ValueError("the zero polynomial has every scalar as a root")
    if len(coeffs) == 1:
        return []
    if coeffs[-1] != 1:
        coeffs = [c / coeffs[-1] for c in coeffs]
    z = sp.Dummy("z")
    eliminant = _rational_eliminant(coeffs, z)
    roots = []
    for candidate in _isolated_candidates(eliminant):
        y = Scalar.rational(0)
        for c in reversed(coeffs):
            y = y * candidate + c
        if not y:
            roots.append(candidate)
    return sorted(roots)


def check_examples():
    a = Scalar.rational(2).sqrt()
    # Reused cubic coefficient records still give independent norm generators.
    cube = Scalar.from_record(RootRecord(poly([-2, 0, 0, 1]), Q(5, 4), Q(13, 10)))
    z = sp.Dummy("z")
    large_norm = _rational_eliminant([cube, cube, cube, Scalar.rational(1)], z)
    assert large_norm.degree() == 81 and large_norm.LC() == 1
    # One of the two real roots of the rational eliminant is extraneous.
    assert roots_over_scalars([-a, 1]) == [a]
    # A repeated root, nonmonic normalization and a degree drop.
    assert roots_over_scalars([6, -6 * a, 3, 0]) == [a]
    # Two irrational roots of X**2 - sqrt(2).
    negative, positive = roots_over_scalars([-a, 0, 1])
    assert negative < 0 < positive and negative == -positive
    assert positive * positive == a and positive == a.sqrt()
    assert roots_over_scalars([a, 0, 1]) == []
    assert roots_over_scalars([5, 0]) == []
    try:
        roots_over_scalars([0, 0])
    except ValueError:
        pass
    else:
        raise AssertionError("zero-polynomial guard failed")
    print("Passed: conjugate filtering, double root, nonmonic and degree-drop "
          "inputs, fourth roots of two, no-real-root and zero-polynomial cases.")


if __name__ == "__main__":
    check_examples()
