"""Collision-free Jones identity testing and optional full reconstruction.

For n crossings, ||V||_1 <= 4^n and its Laurent exponents have absolute value
at most 2*n. Choose M=2^(4*n+2), q=M+2. Reduction into x^2-M*x+1 is injective
on these bounded polynomials. Canonical spin partitions keep the query
subexponential despite the large q: Bell(O(sqrt(n))) states, O(n^2)-bit
coefficients. Jones identity alone is not used as an unknot certificate.
"""
from collections import defaultdict

from .adaptive_potts import adaptive_potts_exact
from .ordering import validate_order
from .potts import _budget
from .potts_exact import PottsLimit, multiply, witness_from_exact


def faithful_colors(crossings):
    if type(crossings) is not int or crossings < 0:
        raise ValueError('crossings must be a nonnegative integer')
    return (1 << (4*crossings+2))+2


def _balanced_digits(value, base, degree_bound, check):
    digits = []
    while value:
        check()
        if len(digits) > degree_bound:
            raise ArithmeticError('quadratic coordinate exceeds its degree bound')
        digit = value % base
        if digit >= base//2:
            digit -= base
        digits.append(digit)
        value = (value-digit)//base
    return digits


def reconstruct_jones(result, *, check=lambda: None):
    """Return integer Laurent coefficients in the standard variable t=A^-4.

Input must be a completed faithful query. Divide its normalization in the
quadratic field exactly, then decode both coordinates in balanced base q-2.
Substituting M=x+x^-1 recovers V(x^-1); negating exponents returns V(t).
"""
    check()
    n, colors = result['crossing_count'], result['q']
    if colors != faithful_colors(n):
        raise ValueError('reconstruction requires the faithful input-sized color count')
    base = colors-2
    c, d = result['unknot_partition']
    norm = c*c+base*c*d+d*d
    if not norm:
        raise ArithmeticError('zero Jones normalization')
    numerator = multiply(result['partition_function'], (c+base*d, -d), colors)
    coordinates = []
    for value in numerator:
        coefficient, remainder = divmod(value, norm)
        if remainder:
            raise ArithmeticError('normalized Jones value is not a quadratic integer')
        coordinates.append(coefficient)
    polynomial = defaultdict(int)
    for offset, coordinate in enumerate(coordinates):
        digits = _balanced_digits(coordinate, base, 2*n, check)
        for degree, coefficient in enumerate(digits):
            if not coefficient:
                continue
            choose = 1
            for k in range(degree+1):
                check()
                polynomial[-(degree-2*k+offset)] += coefficient*choose
                choose = choose*(degree-k)//(k+1)
    polynomial = {degree: c for degree, c in sorted(polynomial.items()) if c}
    if any(abs(degree) > 2*n for degree in polynomial) or sum(map(abs, polynomial.values())) > 1 << (2*n):
        raise ArithmeticError('reconstructed Jones polynomial violates the input bound')
    if (polynomial == {0: 1}) != (result['partition_function'] == result['unknot_partition']):
        raise ArithmeticError('polynomial identity disagrees with the exact query')
    check()
    return polynomial


def faithful_potts_exact(diagram, *, max_states=4096, max_transitions=200_000,
                         order=None, check=lambda: None, statistics=None, shade=None,
                         include_polynomial=False):
    """Decide V(t)=1 exactly, optionally reconstruct V, within local query caps.

Scalar equality implies the polynomial is one, but remains inconclusive for
unknot recognition. Partial/capped queries publish no polynomial-identity result.
Raw quadratic coordinates stay integers; reconstructed polynomial coefficients
are hexadecimal in result metadata for safe JSON output at any bit length.
"""
    _budget(max_states, 'max_states')
    _budget(max_transitions, 'max_transitions')
    if type(include_polynomial) is not bool:
        raise ValueError('include_polynomial must be boolean')
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError('shade must be 0, 1, or None')
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise PottsLimit('faithful Jones filter budget is zero')
    result = adaptive_potts_exact(diagram, colors=faithful_colors(n),
                                  max_states=max_states, max_transitions=max_transitions,
                                  order=order, check=check, statistics=statistics, shade=shade)
    identity = dict(algorithm='quadratic-kronecker-v1', crossing_count=n,
                    is_one=not result['differs'], coefficient_l1_bound_log2=2*n,
                    encoding_base_log2=4*n+2, colors_rule='2^(4*n+2)+2')
    if include_polynomial:
        polynomial = reconstruct_jones(result, check=check)
        result['jones_polynomial'] = dict(variable='t', coefficients_hex=[
            [degree, hex(c)] for degree, c in polynomial.items()])
    check()
    result['polynomial_identity'] = identity
    if statistics is not None:
        statistics.update(result)
    return result


def faithful_potts_obstruction(diagram, **options):
    return witness_from_exact(faithful_potts_exact(diagram, **options),
                              kind='faithful-jones-polynomial-nontrivial')
