#!/usr/bin/env python3
"""Finite numerical checks for the Li sampling theorem. Run with Python 3.

The periodic example has exact Fourier bins. Binary floating point is used
throughout. The example with zeta ordinates is deliberately truncated to two
terms and explicitly accounts for leakage between finite-sample Fourier bins.
Neither example infers a stride from finitely many model atoms.
"""

import cmath
import math
from fractions import Fraction
from math import comb


def regularized_li(index, atoms):
    """Finite model using atoms (theta, multiplicity) and affine compensation."""
    return sum(m * (1 - cmath.exp(1j * index * theta)
                    + 1j * index * math.sin(theta)) for theta, m in atoms)


def forward_difference(values, order):
    """Return all consecutive binomial forward differences of the given order."""
    weights = [(-1) ** (order - j) * comb(order, j) for j in range(order + 1)]
    return [sum(weight * values[n + j] for j, weight in enumerate(weights))
            for n in range(len(values) - order)]


def fourier_mean(values, angle):
    """Demodulate the observations at a specified frequency angle."""
    return sum(v * cmath.exp(-1j * n * angle)
               for n, v in enumerate(values)) / len(values)


def assert_close(actual, expected, tolerance=2e-8):
    error = abs(actual - expected)
    if error > tolerance:
        raise AssertionError(f'error {error:.3g} exceeds {tolerance:g}: '
                             f'{actual!r} versus {expected!r}')


def periodic_check():
    # u=exp(2 pi i j/360), u^q=exp(2 pi i j/60). The two large
    # indices 12 and 72 collide, while bins 1 and 2 have one preimage each.
    full_period = 360
    stride, offset, order = 6, 7, 3
    period = full_period // stride
    indices = [(1, 2), (2, 3), (12, 2), (72, 1)]
    atoms = [(math.tau * j / full_period, m) for j, m in indices]

    def drift(n):
        return (3 - 2j) + (1 + 3j) * n / 8 + (2 - 1j) * n * n / 64

    n_values = range(period + order)
    raw = [regularized_li(stride * n + offset, atoms) for n in n_values]
    contaminated = [value + drift(n) for n, value in enumerate(raw)]
    differences = forward_difference(contaminated, order)
    clean = forward_difference(raw, order)
    assert_close(max(abs(x - y) for x, y in zip(differences, clean)), 0)

    # Test all bins including absent frequencies and the constant bin.
    for k in range(period):
        angle = math.tau * k / period
        collapsed = sum(m * cmath.exp(1j * offset * theta)
                        for (j, m), (theta, _) in zip(indices, atoms)
                        if j % period == k)
        expected = -(cmath.exp(1j * angle) - 1) ** order * collapsed
        assert_close(fourier_mean(differences, angle), expected)

    print('Periodic model: all 60 Fourier bins verified after a quadratic drift.')
    for k, m in ((1, 2), (2, 3)):
        angle = math.tau * k / period
        divided = -fourier_mean(differences, angle) / (cmath.exp(1j * angle) - 1) ** order
        ratio = cmath.phase(divided) / angle
        assert_close(abs(divided), m)
        assert_close(ratio, offset / stride)
        print(f'  bin {k}: modulus {abs(divided):.8f}, phase/angle '
              f'{ratio:.8f} (expected {Fraction(offset, stride)})')

    # At the collision bin the divided coefficient is a vector sum.
    angle = math.tau * 12 / period
    divided = -fourier_mean(differences, angle) / (cmath.exp(1j * angle) - 1) ** order
    expected = abs(2 + cmath.exp(1j * math.tau * offset / stride))
    assert_close(abs(divided), expected)
    print(f'  collision bin 12: modulus {abs(divided):.8f} '
          f'(sqrt(7)), combined multiplicity 3.')


def filter_check():
    # Four clean Fourier bins suffice here because the example has known
    # degree at most three. The theorem uses the entire accumulating tail.
    # For the numerical interpolation check, spread the bins apart.
    base = 120
    stride, order = 2, 3
    period = base // stride
    indices = [(2, 1), (8, 3), (17, 2), (27, 1)]
    atoms = [(math.tau * j / base, m) for j, m in indices]
    taps = [0.50, -0.25, 0.25, 0.50]
    assert_close(sum(taps), 1)
    raw = [sum(a * regularized_li(stride * n + j, atoms)
               for j, a in enumerate(taps)) for n in range(period + order)]
    differences = forward_difference(raw, order)
    observations = []
    for (k, m), (theta, _) in zip(indices, atoms):
        angle = math.tau * k / period
        u = cmath.exp(1j * theta)
        observed = -fourier_mean(differences, angle) / (m * (cmath.exp(1j * angle) - 1) ** order)
        expected = sum(weight * u ** j for j, weight in enumerate(taps))
        assert_close(observed, expected)
        observations.append((u, observed))

    # Evaluate the polynomial interpolant at the fourth roots of unity,
    # then recover the four real taps by Fourier inversion.
    def interpolant(z):
        total = 0j
        for node, value in observations:
            basis = 1 + 0j
            for other, _ in observations:
                if other != node:
                    basis *= (z - other) / (node - other)
            total += value * basis
        return total

    coefficients = [fourier_mean(
        [interpolant(cmath.exp(1j * math.tau * k / 4)) for k in range(4)],
        math.tau * j / 4) for j in range(4)]
    for actual, expected in zip(coefficients, taps):
        assert_close(actual, expected)
    print('Normalized four-tap filter recovered using known multiplicities '
          'and degree bound: ' + ', '.join(f'{v.real:.4f}' for v in coefficients) + '.')


def zeta_pair_check():
    ordinates = [14.134725141734694, 21.022039638771555]
    atoms = [(2 * math.atan(1 / (2 * gamma)), 1) for gamma in ordinates]
    stride, offset, order = 4, 3, 2
    angles = [stride * theta for theta, _ in atoms]
    coefficients = [-(cmath.exp(1j * angle) - 1) ** order
                    * cmath.exp(1j * offset * theta)
                    for angle, (theta, _) in zip(angles, atoms)]
    print('Two-ordinate zeta model (positive ordinates only):')
    for count in (256, 1024):
        raw = [regularized_li(stride * n + offset, atoms)
               for n in range(count + order)]
        differences = forward_difference(raw, order)
        measured = fourier_mean(differences, angles[0])
        delta = angles[1] - angles[0]
        geometric_mean = ((1 - cmath.exp(1j * count * delta)) /
                          (count * (1 - cmath.exp(1j * delta))))
        assert_close(measured, coefficients[0] + coefficients[1] * geometric_mean)
        leakage_bound = 2 * abs(coefficients[1]) / (count * abs(1 - cmath.exp(1j * delta)))
        actual_leakage = abs(measured - coefficients[0])
        if actual_leakage > leakage_bound + 1e-12:
            raise AssertionError('two-bin leakage exceeds the geometric-sum bound')
        print(f'  {count} samples: absolute coefficient error {actual_leakage:.3e}, '
              f'bound {leakage_bound:.3e}.')


if __name__ == '__main__':
    periodic_check()
    filter_check()
    zeta_pair_check()
    print('All finite checks passed.')
