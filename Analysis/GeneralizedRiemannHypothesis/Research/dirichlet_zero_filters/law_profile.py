"""Evaluate the proved limiting law for the extra filter width (Python 3).

Computed decimals are illustrations. The distribution is determined by the
implicit equations in the paper and is independent of these calculations.
"""
from math import atan, cos, pi, sin, sqrt, tan


def increasing_inverse(function, target, left, right):
    for _ in range(65):
        middle = (left + right) / 2
        if function(middle) < target:
            left = middle
        else:
            right = middle
    return (left + right) / 2


def excess(u):
    if u == 0 or u == pi:
        return 0.0
    y = increasing_inverse(lambda theta: tan(theta) - theta, u, 0, pi/2)
    # sin(u + z)/z decreases until the first zero of sin(u + z).
    z = increasing_inverse(lambda x: -sin(u+x)/x, -cos(y), 0, pi-u)
    return 2*z


def cdf(value):
    if value <= 0:
        return 0.
    if value >= pi:
        return 1.
    peak = atan(2/pi)
    left = increasing_inverse(excess, value, 0, peak)
    right = increasing_inverse(lambda u: -excess(u), -value, peak, pi)
    return (left + (pi-right))/pi


if __name__ == "__main__":
    for t in [0.25, 0.5, 0.75, 0.90]:
        print(f"P(X <= {t:.2f} pi) = {cdf(t*pi):.9f}")
    median = increasing_inverse(cdf, 0.5, 0, pi)
    print(f"Median of X/pi = {median/pi:.9f}")
    Y_pi = increasing_inverse(lambda theta: tan(theta) - theta, pi, 0, pi/2)
    lower = (1+cos(Y_pi))/(2*pi)
    t0 = pi/2
    upper = 2*sqrt(2*t0**3)/(pi*(1+t0**2))
    print(f"Lower endpoint coefficient = {lower:.9f}")
    print(f"Upper endpoint coefficient = {upper:.9f}")
