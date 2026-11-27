"""Exact tests of the folded Fourier coefficient decoder over Q(sqrt(2)).

Each pair (a,b) represents a+b*sqrt(2).  The lattice positions are eighths.
For A=128 log(2), the Gaussian weight at u=j/8 is exactly 2^(-2*j*j).
No floating point is used in forming the data or decoding the multiplicities.
"""
from fractions import Fraction as F
from itertools import product
import json


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def scale(x, factor):
    return x[0] * factor, x[1] * factor


def sign(x):
    a, b = x
    if a == 0:
        return (b > 0) - (b < 0)
    if b == 0 or (a > 0) == (b > 0):
        return (a > 0) - (a < 0)
    # Opposite signs are decided by a positive squaring comparison.
    diff = a * a - 2 * b * b
    return ((diff > 0) - (diff < 0)) * (1 if a > 0 else -1)


def absolute(x):
    return scale(x, -1) if sign(x) < 0 else x


def weight(j):
    return F(1, 1 << (2*j*j))


def groups(residue, depth):
    if residue <= 2 or residue >= 6:
        centre = residue if residue <= 2 else residue - 8
        return [(centre,)] + [(centre-8*k, centre+8*k)
                              for k in range(1, depth+1)]
    centre = residue - 4
    return [(centre-(8*k+4), centre+(8*k+4)) for k in range(depth+1)]


def project(real, imag, j, other=None):
    if other is None:
        value = real
    else:
        numerator = sub(imag, scale(real, F(other, 8)))
        value = scale(numerator, F(8, j-other))
    return scale(value, 1/weight(j))


def nearest(value, bound):
    winner = None
    best = None
    for digits in product(range(bound+1), repeat=2):
        distance = absolute(sub(value, digits))
        if best is None or sign(sub(distance, best)) < 0:
            best, winner = distance, digits
    return winner


def encode(data):
    real, imag = (0, 0), (0, 0)
    for j, digits in data.items():
        amplitude = scale(digits, weight(j))
        real = add(real, amplitude)
        imag = add(imag, scale(amplitude, F(j, 8)))
    return real, imag


def check_case(residue, variant, with_noise):
    layers = groups(residue, 4)
    data = {}
    for layer in layers:
        for j in layer:
            bound = (2*(8+abs(j)))//8
            data[j] = ((abs(11*j+variant) % (bound+1)),
                       (abs(5*j-2*variant) % (bound+1)))
    real, imag = encode(data)
    # Ask for recovery through the third layer only; the last two act as
    # completely known synthetic tails from the viewpoint of this checker.
    # The decoder sees only their contribution to the folded number.
    tested = layers[:3]
    radius = max(abs(j) for layer in tested for j in layer)
    if with_noise:
        one_plus_r = 1+F(radius, 8)
        # D=8 for h=B=2. Split the admissible error between the coordinates.
        tol = weight(radius)/(4*one_plus_r*8*one_plus_r)
        real = add(real, (tol/2, 0))
        imag = add(imag, (-tol/2, 0))
    count = 0
    for layer in tested:
        recovered = {}
        for index, j in enumerate(layer):
            other = layer[1-index] if len(layer) == 2 else None
            value = project(real, imag, j, other)
            bound = (2*(8+abs(j)))//8
            recovered[j] = nearest(value, bound)
            if recovered[j] != data[j]:
                raise AssertionError((residue, variant, j, recovered[j], data[j]))
            count += 1
        dr, di = encode(recovered)
        real, imag = sub(real, dr), sub(imag, di)
    return count


if __name__ == "__main__":
    total = sum(check_case(r, v, noisy)
                for r in range(8) for v in range(5) for noisy in (False, True))
    print(json.dumps({"coefficient_field": "Q(sqrt(2))", "residue_classes": 8,
                      "profiles_per_class": 5, "error_modes": 2,
                      "labelled_vectors_recovered": total,
                      "arithmetic": "exact rational pairs and integer comparisons"},
                     indent=2))
