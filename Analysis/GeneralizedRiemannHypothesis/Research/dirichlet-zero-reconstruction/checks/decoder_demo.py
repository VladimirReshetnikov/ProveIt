"""Evaluate the paper's zero-sum decoder for the conjugate quartic characters mod 5.

Requires scipy and mpmath. complex_zeros.py supplies sign-change approximations.
Run from this directory with python decoder_demo.py. This illustrates the
normalization and orientation; it does not certify completeness of the zero list.
"""
import cmath
import math

from scipy.integrate import quad
from scipy.special import k0

from complex_zeros import sign_changes


BANDWIDTH = 8.0
PRIME = 2
CENTERS = (0.0, 36.0)
HALF_WIDTH = 36.0
ELL = math.log(PRIME)


def four_uniform_density(v):
    """Density of a sum of four independent uniform[-B,B] variables."""
    w = (4 * BANDWIDTH - abs(v)) / (2 * BANDWIDTH)
    if w < 0:
        return 0.0
    return (w ** 3 - 4 * max(w - 1, 0) ** 3) / (12 * BANDWIDTH)


def transform(t, derivative):
    """Fourier transform of eta*sinc^4, or its first derivative, at b=1."""
    def integrand(v):
        u = t + v
        value = math.exp(-math.cosh(u)) * four_uniform_density(v)
        return -math.sinh(u) * value if derivative else value

    half_support = 4 * BANDWIDTH
    integral, error = quad(
        integrand, -half_support, half_support, epsabs=2e-13, epsrel=2e-13,
        points=[-2 * BANDWIDTH, 0, 2 * BANDWIDTH]
    )
    if error > 2e-11:
        raise ArithmeticError("Quadrature did not reach the stated tolerance")
    return math.pi * integral / k0(1)


def term(ordinate, center):
    t = ordinate - center
    localized = transform(t, False) + transform(t, True) / (1j * ELL)
    return cmath.exp(1j * ordinate * ELL) * localized


def main():
    height = max(CENTERS) + HALF_WIDTH
    positive = {sign: list(map(float, sign_changes(sign, height))) for sign in [1, -1]}
    for center in CENTERS:
        print(f"p={PRIME}, b=1, B={BANDWIDTH:g}, U={center:g}, H={HALF_WIDTH:g}")
        results = {}
        for sign in [1, -1]:
            signed = positive[sign] + [-t for t in positive[-sign]]
            data = [t for t in signed if abs(t - center) <= HALF_WIDTH]
            result = -math.sqrt(PRIME) / ELL * sum(term(t, center) for t in data)
            results[sign] = result
            difference = abs(result - sign * 1j)
            print(f"chi(2) = {sign:+d}i, {len(data)} ordinates, decoder = "
                  f"{result.real:+.8f}{result.imag:+.8f}i, error = {difference:.8f}")
            if difference > 0.45:
                raise ArithmeticError("Decoder did not isolate the expected character value")
        if center == 0 and abs(results[-1] - results[1].conjugate()) > 1e-11:
            raise ArithmeticError("Conjugation symmetry failed")
    print("Numerical illustration using the mod-5 sign-change scan, without a certified zero count.")


if __name__ == "__main__":
    main()
