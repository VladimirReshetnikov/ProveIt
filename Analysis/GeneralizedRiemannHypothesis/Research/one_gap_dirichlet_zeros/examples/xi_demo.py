#!/usr/bin/env python3
"""Recover the first two positive Riemann-Xi ordinates from analytic samples.

Run with Python >=3.9 and mpmath 1.3.0: python xi_demo.py
This is a floating-point illustration, not an interval certificate. No list
of higher zeros is an input. All coordinates u are in units of 'scale'.
"""
from math import comb
import mpmath as mp


def xi(t):
    s = mp.mpf('0.5') + mp.j * t
    return s * (s - 1) * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s) / 2


def log_coefficients(scale, radius, deflate, count, degree):
    """Cauchy coefficients of log(Xi(scale*u)/Xi(0)), optionally pair-deflated.

    Evenness and conjugation reduce the trapezoidal rule to a quadrant.
    Continue the logarithm on that quadrant by successive phase differences.
    """
    assert count % 4 == 0 and degree < count
    normalizer = xi(0)
    angles = [2 * mp.pi * j / count for j in range(count // 4 + 1)]
    logs = []
    previous = None
    phase = mp.mpf(0)
    for theta in angles:
        u = radius * mp.expj(theta)
        value = xi(scale * u) / normalizer
        if deflate:
            value /= 1 - u**2
        if previous is None:
            assert value.real > 0 and abs(value.imag) < mp.eps**mp.mpf('0.8')
        else:
            step = mp.arg(value / previous)
            assert abs(step) < mp.pi / 2
            phase += step
        logs.append(mp.log(abs(value)) + mp.j * phase)
        previous = value
    assert abs(phase) < mp.eps**mp.mpf('0.8')
    coefficients = [mp.mpf(0)] * (degree + 1)
    for n in range(2, degree + 1, 2):
        interior = mp.fsum((logs[j] * mp.expj(-n * angles[j])).real
                           for j in range(1, count // 4))
        ends = logs[0].real + (-1)**(n // 2) * logs[-1].real
        coefficients[n] = (4 * interior + 2 * ends) / (count * radius**n)
    return coefficients


def balance(coefficients, p):
    """Return u and the endpoint readout K in units with endpoints +/-1.

    The true odd-power field from the outer zeros is
    H_p(u) = p * [w^p] log F(u+w). The marked endpoints contribute
    2/(1+u)^p - 1/(1-u)^p. Reparameterizing by delta avoids subtracting
    almost equal endpoint fields when that difference is about 14**(-p).
    """
    assert p >= 3 and p % 2 == 1
    shifted = [p * comb(n, p) * coefficients[n]
               for n in range(p, len(coefficients))]
    log_two = mp.log(2)
    delta = mp.mpf(0)
    for iteration in range(200):
        u = mp.tanh((log_two + delta) / (2 * p))
        outer = mp.polyval(shifted[::-1], u)
        updated = mp.log1p(outer * (1 + u)**p / 2)
        if abs(updated - delta) <= 50 * mp.eps * abs(updated):
            break
        delta = updated
    else:
        raise ArithmeticError('marked-balance iteration did not converge')
    readout = -2 * mp.expm1(delta) / (1 + u)**p
    assert readout > 0 and abs(readout + outer) <= 1000 * mp.eps * readout
    return u, readout


def atom(r, u, p):
    """A unit positive shell's discrepancy; expm1 stabilizes the difference."""
    return (r + u)**(-p) * mp.expm1(2 * p * mp.atanh(u / r)) / (2 * p * u)


def solve_decreasing(function, target):
    # In these experiments the shell lies above 1. Expanding on the right
    # avoids supplying the ordinate (or a guessed numerical root) as input.
    left, right = mp.mpf(1), mp.mpf(2)
    if function(left) < target:
        return left
    while function(right) > target:
        right *= 2
    for _ in range(220):
        middle = (left + right) / 2
        if function(middle) > target:
            left = middle
        else:
            right = middle
    return (left + right) / 2


def paired_bounds(p, u, k, v, next_k):
    discrepancy = k / (2 * p * u)
    next_discrepancy = next_k / (2 * (p + 2) * v)
    low = solve_decreasing(lambda r: atom(r, u, p), discrepancy)
    high = solve_decreasing(lambda r: atom(r, v, p + 2) / atom(r, u, p),
                            next_discrepancy / discrepancy)
    return low, high, discrepancy / atom(high, u, p)


def measure(p_values, scale, radius, deflate, count):
    orders = sorted(set(p_values) | {p + 2 for p in p_values})
    coeffs = log_coefficients(scale, radius, deflate, count, max(orders) + 40)
    readings = {p: balance(coeffs, p) for p in orders}
    second_moment = -coeffs[2]
    rows = []
    paired = []
    for p in p_values:
        u, k = readings[p]
        v, next_k = readings[p + 2]
        ratio = mp.sqrt(k / next_k)
        low, high, mass = paired_bounds(p, u, k, v, next_k)
        paired.append((p, scale * low, scale * high, mass))
        if deflate:
            # Multiplicity per sign, fitted with the estimated radius.
            pair_field = (ratio - u)**(-p) - (ratio + u)**(-p)
            rows.append((p, scale * u, k, scale * ratio, k / pair_field))
        else:
            discrepancy = k / (2 * p * u)
            lower = discrepancy**(-mp.mpf(1) / (p + 1))
            upper = u + (second_moment / ((1 - u)**2 * discrepancy))**(
                mp.mpf(1) / (p - 1))
            rows.append((p, u, k, lower, upper, ratio))
    return second_moment, rows, paired


def pretty(x, digits=12):
    return mp.nstr(x, digits, min_fixed=-3, max_fixed=4)


def print_paired(rows):
    print('Calibrated one-shell enclosures (floating evaluations of exact inequalities).')
    print(' p       one-shell lower        paired-ratio upper        upper mass per sign')
    for p, low, high, mass in rows:
        print(f'{p:3d} {pretty(low, 18):>23} {pretty(high, 18):>25} {pretty(mass, 17):>26}')


def compare(rows, repeated):
    # Relative differences, including tiny readouts: both configurations must
    # agree on all digits printed in the table, with extra margin.
    error = max(abs(a - b) / max(abs(a), abs(b))
                for row, other in zip(rows, repeated)
                for a, b in zip(row[1:], other[1:]))
    assert error < mp.mpf('1e-18'), error
    return error


def main():
    first_orders = [9, 17, 33, 49, 65]
    second_orders = [7, 15, 31, 63, 127]
    with mp.workdps(100):
        _, first_repeat, first_paired_repeat = measure(first_orders, 1, mp.mpf('4.5'), False, 320)
    with mp.workdps(135):
        moment, first, first_paired = measure(first_orders, 1, mp.mpf('5'), False, 512)
        error = max(compare(first, first_repeat), compare(first_paired, first_paired_repeat))
        print('Experiment 1. Artificial endpoints -1,+1, with weights 2,1.')
        print('All measurements use Xi(s) values; no zero ordinate was supplied.')
        print('S2 = -Xi\'\'(0)/(2 Xi(0)) =', pretty(moment, 22))
        print(' p    marked balance x       K_p                lower L_p'
              '          upper U_p          sqrt(K_p/K_{p+2})')
        for p, u, k, low, high, ratio in first:
            print(f'{p:3d} {pretty(u):>19} {pretty(k):>18} {pretty(low):>17}'
                  f' {pretty(high):>18} {pretty(ratio):>21}')
        print('Maximum relative change, independent numerical settings:', pretty(error, 3))
        print_paired(first_paired)
        first_reference = mp.im(mp.zetazero(1))
        print('Comparison only: Im(zetazero(1)) =', pretty(first_reference, 22))
        print()
    with mp.workdps(100):
        scale = mp.im(mp.zetazero(1))
        _, second_repeat, second_paired_repeat = measure(second_orders, scale, mp.mpf('1.08'), True, 320)
    with mp.workdps(135):
        scale = mp.im(mp.zetazero(1))
        _, second, second_paired = measure(second_orders, scale, mp.mpf('1.10'), True, 512)
        error = max(compare(second, second_repeat), compare(second_paired, second_paired_repeat))
        print('Experiment 2. Gap endpoints +/-d, d = Im(zetazero(1)).')
        print('Remove 1-(t/d)^2 analytically, then give the endpoints weights 2,1.')
        print('Only d is used; the second ordinate is read after the measurements.')
        print(' p    marked balance x       d^p K_p            ratio radius (t units)'
              '    fitted mass per sign')
        for p, x, k, ratio, mass in second:
            print(f'{p:3d} {pretty(x):>19} {pretty(k):>18} {pretty(ratio):>27}'
                  f' {pretty(mass):>23}')
        print('Maximum relative change, independent numerical settings:', pretty(error, 3))
        print_paired(second_paired)
        second_reference = mp.im(mp.zetazero(2))
        print('Comparison only: Im(zetazero(2)) =', pretty(second_reference, 22))
        print('All figures are rounded floating-point values, not certified enclosures.')


if __name__ == '__main__':
    main()
