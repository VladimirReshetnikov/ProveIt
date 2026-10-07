#!/usr/bin/env python3
"""Deterministic executable tests; no assert statements (also run with -O)."""
from fractions import Fraction
import json
from exact import (Q5, ZERO, ONE, PHI, RHO, CURVATURE, natural,
                   bernoulli_through, f_derivatives, inverse_series,
                   radial_coefficients, coefficient_transfer, partition_counts,
                   exponent_terms, gaussian_moment, multiply_series)
from inverse import inverse_polynomials, series_function, smul
from oracle import (radial_oracle, direct_finite_products, enumerate_partitions,
                    bernoulli_number, eulerian_derivative)


def check(condition, message):
    if not condition:
        raise RuntimeError('test failed: '+message)


def rejects(exception, function, *arguments):
    try:
        function(*arguments)
    except exception:
        return
    raise RuntimeError('expected '+exception.__name__+' from '+function.__name__)


def main():
    expected = [ONE, Q5(Fraction(239,120), 1),
                Q5(Fraction(232801,28800), Fraction(431,120)),
                Q5(Fraction(640181519,10368000), Fraction(795361,28800)),
                Q5(Fraction(3268837156801,4976640000), Fraction(3045555791,10368000))]
    actual = radial_coefficients(4)
    check(actual == expected, 'published radical coefficients')
    check(actual == radial_oracle(4), 'independent Gaussian oracle through c4')
    for k in range(5):
        check(radial_coefficients(k) == actual[:k+1], 'whole-degree truncation')
    check(PHI*PHI == PHI+1 and RHO+RHO*RHO == ONE, 'golden-ratio identities')
    check(CURVATURE == 3*PHI-4, 'Gaussian curvature')
    check(Q5(2, 3)/Q5(2, 3) == ONE, 'quadratic-field division')
    check(Q5(2, 3)**-2 * Q5(2, 3)**2 == ONE, 'negative exponent')
    check(bernoulli_through(10) == [bernoulli_number(i) for i in range(11)], 'Bernoulli algorithms')
    for z in (RHO, RHO**2):
        fd = f_derivatives(z, 10)
        check(fd[1:] == [eulerian_derivative(z, m) for m in range(1, 11)], 'derivative algorithms')
    e = exponent_terms(4)
    check(all((p-d)%2 == 0 for d in range(1,9) for p in e[d]), 'whole-degree parity')
    transfer = coefficient_transfer(actual)
    check(transfer[1] == {1: actual[1]}, 'd1')
    check(transfer[2] == {0: -actual[1]/2, 2: actual[2]}, 'd2')
    check(transfer[3] == {1: -3*actual[2]/2, 3: actual[3]}, 'd3')
    check(transfer[4] == {0: 3*actual[2]/4, 2: -3*actual[3], 4: actual[4]}, 'd4')
    inverse = inverse_polynomials(4)
    check(inverse[0] == {(1,0,0,0,0): Fraction(1), (0,1,0,0,0): Fraction(-1)}, 'inverse P1')
    check(inverse[1] == {(2,0,0,0,0): Fraction(-1,2), (1,0,0,0,0): Fraction(1), (1,1,0,0,0): Fraction(1), (0,1,0,0,0): Fraction(-1), (0,0,1,0,0): Fraction(-1)}, 'inverse P2')
    # inverse_polynomials also checks every defining residual through order four.
    counts = partition_counts(400)
    check(counts == direct_finite_products(400), 'independent finite-product DP through 400')
    check(counts[:36] == enumerate_partitions(35), 'direct integer-partition enumeration through 35')
    check(counts[:11] == [0,0,0,1,1,2,3,3,4,6,6], 'initial exact counts')
    for f in (radial_coefficients, radial_oracle, exponent_terms, partition_counts,
              direct_finite_products, enumerate_partitions, bernoulli_through,
              bernoulli_number, gaussian_moment, inverse_polynomials):
        rejects(ValueError, f, -1)
        rejects(TypeError, f, True)
        rejects(TypeError, f, Fraction(1,2))
    rejects(TypeError, Q5, '1/2')
    rejects(TypeError, Q5, 0.5)
    rejects(TypeError, Q5, True)
    rejects(TypeError, pow, ONE, Fraction(1,2))
    rejects(ZeroDivisionError, ZERO.inverse)
    rejects(ZeroDivisionError, inverse_series, [ZERO], 2)
    rejects(ValueError, inverse_series, [], 2)
    rejects(ValueError, coefficient_transfer, [])
    rejects(ValueError, coefficient_transfer, [ZERO])
    rejects(ValueError, eulerian_derivative, RHO, 0)
    rejects(ValueError, multiply_series, [ONE], [ONE], -1)
    rejects(ValueError, f_derivatives, RHO, -1)
    for invalid in (True, Fraction(1,2)):
        rejects(TypeError, f_derivatives, RHO, invalid)
    for invalid in (0.5, True):
        for degree in (0, 1):
            rejects(TypeError, f_derivatives, invalid, degree)
    formal_one = [{(0,): Fraction(1)}]
    for invalid, exception in ((-1, ValueError), (True, TypeError), (Fraction(1,2), TypeError)):
        rejects(exception, series_function, formal_one, invalid)
        rejects(exception, smul, formal_one, formal_one, invalid)
    print(json.dumps({'status': 'pass', 'radial_oracle_order': 4, 'inverse_residual_order': 4,
                      'finite_product_agreement_through': 400,
                      'partition_enumeration_through': 35,
                      'negative_argument_guards': 'pass',
                      'optimization_safe': 'tests use explicit exceptions'}, sort_keys=True))


if __name__ == '__main__':
    main()
