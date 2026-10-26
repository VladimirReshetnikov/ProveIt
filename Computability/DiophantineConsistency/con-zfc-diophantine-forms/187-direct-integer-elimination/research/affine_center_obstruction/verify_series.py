#!/usr/bin/env python3
"""Exact restricted affine-scale obstruction for the whole-product center.

Only Python's standard library is used.  This is a coefficient calculation,
not a search for a consistency witness and not a proof of global optimality.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import argparse
import json

NAMES = ('X', 'Y', 'k', 'U', 'b', 'c')
WEIGHTS = (2, 2, 1, 7, 4, 3)
ZERO = (0,) * 6

def require(condition, message):
    if not condition:
        raise ValueError(message)

def scalar(value):
    return {ZERO: Fraction(value)} if value else {}

def variable(index):
    powers = [0] * 6
    powers[index] = 1
    return {tuple(powers): Fraction(1)}

def add(*polynomials):
    result = defaultdict(Fraction)
    for polynomial in polynomials:
        for powers, coefficient in polynomial.items():
            result[powers] += coefficient
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}

def scale(polynomial, coefficient):
    return {powers: value * coefficient for powers, value in polynomial.items()
            if value * coefficient}

def multiply(left, right):
    result = defaultdict(Fraction)
    for a, c in left.items():
        for b, d in right.items():
            powers = tuple(x + y for x, y in zip(a, b))
            result[powers] += c * d
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}

def square(polynomial):
    return multiply(polynomial, polynomial)

def weight(powers):
    return sum(x * y for x, y in zip(powers, WEIGHTS))

def homogeneous(polynomial, degree):
    return {powers: coefficient for powers, coefficient in polynomial.items()
            if weight(powers) == degree}

def nonpolynomial_part(polynomial):
    return {powers: coefficient for powers, coefficient in polynomial.items()
            if any(exponent < 0 for exponent in powers)}

def encode(polynomial):
    return [[list(powers), str(coefficient)]
            for powers, coefficient in sorted(polynomial.items())]

def calculate():
    X, Y, k, U, b, c = map(variable, range(6))
    A = add(multiply(X, Y), Y, scalar(1))
    E = add(scalar(1), multiply(X, multiply(square(Y), square(k))),
            multiply(square(X), multiply(square(square(Y)), square(k))))
    delta = add(square(A), scalar(-1))
    a = multiply(delta, multiply(square(U), E))
    f = add(scalar(1), scale(a, 2))
    V = add(multiply(f, b), scale(c, -1))
    G = multiply(E, add(scalar(1), a))
    H = scale(multiply(G, square(V)), 16)
    leading = (7, 11, 4, 3, 1, 0)
    require(homogeneous(H, 130) == {tuple(2*x for x in leading): Fraction(64)},
            'incorrect leading term')
    root = {leading: Fraction(8)}
    pieces = {65: root.copy()}
    for degree in range(64, 36, -1):
        difference = add(homogeneous(H, 65+degree),
                         scale(homogeneous(square(root), 65+degree), -1))
        piece = {tuple(x-y for x, y in zip(powers, leading)): coefficient/16
                 for powers, coefficient in difference.items()}
        if piece:
            require(all(weight(powers) == degree for powers in piece), 'weight')
            pieces[degree] = piece
            root = add(root, piece)
        require(not add(homogeneous(H, 65+degree),
                        scale(homogeneous(square(root), 65+degree), -1)),
                'formal square-root recurrence failed')
    require(all(not nonpolynomial_part(piece) for degree, piece in pieces.items()
                if degree > 41), 'earlier nonpolynomial term')
    expected = {
        41: {(-1, 7, 4, 3, 1, 0): Fraction(3)},
        39: {(-2, 7, 4, 3, 1, 0): Fraction(-3),
             (-1, 6, 4, 3, 1, 0): Fraction(12)},
        37: {(-3, 7, 4, 3, 1, 0): Fraction(3),
             (-2, 6, 4, 3, 1, 0): Fraction(-15),
             (-1, 5, 4, 3, 1, 0): Fraction(15)},
    }
    for degree, polynomial in expected.items():
        require(nonpolynomial_part(pieces[degree]) == polynomial,
                'incorrect critical Laurent coefficients')
    # The only nonconstant affine scale able to cancel the first two
    # nonpolynomial homogeneous components is a scalar multiple of X+1.
    product = multiply(add(X, scalar(1)), root)
    require(not nonpolynomial_part(homogeneous(product, 43)), 'affine 43 cut')
    require(not nonpolynomial_part(homogeneous(product, 41)), 'affine 41 cut')
    require(nonpolynomial_part(homogeneous(product, 39)) ==
            {(-1, 6, 4, 3, 1, 0): Fraction(-3)}, 'affine 39 obstruction')
    return {
        'status': 'PASS',
        'ring': 'Q[X,Y,k,U,b,c]',
        'weights': dict(zip(NAMES, WEIGHTS)),
        'target': '16*G*V^2',
        'target_monomials': len(H),
        'root_leading_weight': 65,
        'critical_nonpolynomial_components':
            {str(degree): encode(polynomial) for degree, polynomial in expected.items()},
        'affine_X_plus_one_first_nonpolynomial_weight': 39,
        'affine_X_plus_one_first_nonpolynomial_component':
            encode(nonpolynomial_part(homogeneous(product, 39))),
        'proved_restricted_lower_bound': 106,
        'scope': ('For any nonzero affine r in Q[X,Y] and polynomial C in '
                  'Q[X,Y,k,U,b,c], the weighted degree of '
                  'C^2-16*r^2*G*V^2 is at least 106. '
                  'This says nothing about other encodings or arbitrary nonlinear scales.'),
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = calculate()
    content = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.write_text(content)
    print(content, end='')

if __name__ == '__main__':
    main()
