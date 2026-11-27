"""Numerical examples for exterior spectral shells and multiplicity recovery.

All zeros in this file are synthetic. Run with Python 3; only the standard
library is required. The checks illustrate the lemmas and do not verify any
Dirichlet L-function or provide a numerical test of GRH.
"""

import cmath
import math


def cayley(rho):
    return 1 - 1 / rho


def symmetric_data():
    """Return (zero, multiplicity) pairs with the Dirichlet reflection."""
    data = []
    for rho, multiplicity in [
        (0.25 + 1.25j, 2),
        (0.25 - 1.25j, 1),
        (0.375 + 120j, 7),
    ]:
        data.append((rho, multiplicity))
        data.append((1 - rho.conjugate(), multiplicity))
    data.append((0.5 + 3j, 1))
    return data


def test_reflection_and_high_zero(stride, offset):
    for rho, multiplicity in symmetric_data():
        u = cayley(rho)
        reflected = cayley(1 - rho.conjugate())
        assert abs(reflected - 1 / u.conjugate()) < 2e-15
        assert abs(reflected**stride - 1 / (u**stride).conjugate()) < 1e-14
        if rho.real < 0.5 and rho.imag > 100:
            z = u**stride
            residue = multiplicity * u**offset
            assert round(abs(residue)) == multiplicity
            observed_ratio = cmath.phase(residue) / cmath.phase(z)
            assert math.isclose(observed_ratio, offset / stride, abs_tol=1e-13)
            print(f"High exterior node: |A/(z-1)^d| = {abs(residue):.9f}")
            print(f"Rounded multiplicity = {round(abs(residue))}")
            print(f"Recovered offset/stride = {observed_ratio:.9f}")


def test_demodulation(stride, offset, difference_order):
    # Here A is the coefficient of z^n in the d-th forward difference.
    atoms = []
    for rho, multiplicity in symmetric_data():
        u = cayley(rho)
        z = u**stride
        amplitude = -multiplicity * u**offset * (z - 1)**difference_order
        atoms.append((z, amplitude))

    target, coefficient = atoms[0]
    assert all(abs(z) <= abs(target) + 1e-15 for z, _ in atoms)
    assert abs(abs(atoms[2][0]) - abs(target)) < 1e-15
    # Demodulating by the target divides out its exponential growth and phase.
    # The geometric sum for each competitor gives an error <= C/length,
    # independent of the starting index of the window.
    error_constant = sum(
        2 * abs(amplitude) / abs(1 - z / target)
        for z, amplitude in atoms[1:]
    )
    for length in (100, 400, 1600):
        errors = []
        for start in (0, 37, 123):
            averages = []
            for z, amplitude in atoms:
                ratio = z / target
                samples = (ratio**n for n in range(start, start + length))
                averages.append(amplitude * sum(samples) / length)
            error = abs(sum(averages) - coefficient)
            assert error <= error_constant / length + 1e-10
            errors.append(error)
        print(f"Window {length:4}: max observed error {max(errors):.6g}, "
              f"uniform bound {error_constant / length:.6g}")


if __name__ == "__main__":
    test_reflection_and_high_zero(stride=3, offset=5)
    test_demodulation(stride=3, offset=5, difference_order=3)
    print("Synthetic reflection, rounding and demodulation checks passed.")
