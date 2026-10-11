"""Exact functional-monomial normal forms, using rational arithmetic.

A monomial is a sorted tuple of derivative indices.  For example,
(0, 0, 2, 2) represents u_0**2*u_2**2.  Polynomials are dictionaries
from monomials to fractions.  This module has no third-party dependency.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache


def add(a, b, scale=Fraction(1)):
    result = dict(a)
    for monomial, value in b.items():
        result[monomial] = result.get(monomial, Fraction(0)) + scale * value
        if not result[monomial]:
            del result[monomial]
    return result


def derivative(polynomial):
    result = {}
    for monomial, coefficient in polynomial.items():
        for index, multiplicity in Counter(monomial).items():
            target = list(monomial)
            target.remove(index)
            target.append(index + 1)
            target = tuple(sorted(target))
            result[target] = result.get(target, Fraction(0)) + multiplicity * coefficient
    return {m: c for m, c in result.items() if c}


def functional(monomial):
    return not monomial or monomial[-1] == 0 or monomial.count(monomial[-1]) > 1


@lru_cache(maxsize=None)
def reduce_monomial(monomial):
    if functional(monomial):
        return {monomial: Fraction(1)}, {}
    index = monomial[-1]
    lower = tuple(sorted(monomial[:-1] + (index - 1,)))
    multiplicity = lower.count(index - 1)
    remainder = add({monomial: Fraction(1)}, derivative({lower: Fraction(1)}),
                    -Fraction(1, multiplicity))
    normal, primitive = {}, {lower: Fraction(1, multiplicity)}
    for target, coefficient in remainder.items():
        normal_target, primitive_target = reduce_monomial(target)
        normal = add(normal, normal_target, coefficient)
        primitive = add(primitive, primitive_target, coefficient)
    return normal, primitive


def normal_form(polynomial):
    normal, primitive = {}, {}
    for monomial, coefficient in polynomial.items():
        n, h = reduce_monomial(monomial)
        normal = add(normal, n, coefficient)
        primitive = add(primitive, h, coefficient)
    return normal, primitive


def gamma_successor(polynomial):
    return add({(0,) + m: c for m, c in polynomial.items()}, derivative(polynomial), -1)


def serialize(polynomial):
    return [{"indices": list(m), "coefficient": str(c)} for m, c in sorted(polynomial.items())]
