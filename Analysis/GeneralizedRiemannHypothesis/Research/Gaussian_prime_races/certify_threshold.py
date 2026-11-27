#!/usr/bin/env python3
"""Enclose the Gaussian prime race threshold using exact rational arithmetic.

External input: Platt's database of the first consecutive zeros of the
primitive L-function 4.3, reproduced below to fewer places. The LMFDB record
and its Reliability page specify the completeness and rounding guarantee.
The next listed ordinate is 32.5921865271171551308..., strictly above 32.
https://www.lmfdb.org/L/1/2e2/4.3/r1/0/0
https://www.lmfdb.org/L/1/2e2/4.3/r1/0/0/Reliability
"""

from fractions import Fraction as F
from math import factorial


CENTERS = tuple(map(F, (
    "6.0209489046975966549025", "10.2437703041665545521377",
    "12.9880980123124225074531", "16.3426071045872221949768",
    "18.2919931961235348385260", "21.4506113439834604972009",
    "23.2783765204595315318195", "25.7287564250887275672650",
    "28.3596343430253277856516", "29.6563840145931527218099",
)))
RADIUS = F(1, 10**21)
SCALE = 10**30
H_LOW, H_HIGH = F("0.04007656562"), F("0.04007656609")
# Discovery only. Set t close to (2n+1)pi/gamma_1, so the first cosine is
# -1. For the next six ordinates r_j=gamma_j/gamma_1, seek integer n with
# n*r_j near (1-r_j)/2 modulo 1. Weight each phase discrepancy by
# sqrt(2*exp(-h*gamma_j^2)). LLL reduction and a nearby-lattice-point
# search gave n=56786717192. Only the exact rational t below enters the proof.
WITNESS = F("59260005815.44527175543962534")


def round_outward(lo, hi):
    return F((lo * SCALE).__floor__(), SCALE), F((hi * SCALE).__ceil__(), SCALE)


def atan_bracket(x):
    """Consecutive partial sums of the alternating arctan series."""
    partial = sum((-1)**j * x**(2*j + 1) / (2*j + 1) for j in range(33))
    return partial - x**67/67, partial


def pi_bracket():
    a, b = atan_bracket(F(1, 5))
    c, d = atan_bracket(F(1, 239))
    return round_outward(16*a - 4*d, 16*b - 4*c)


def exp_minus(x):
    """Enclose exp(-x) by an alternating series at x/64 and integer powers."""
    y = x/64
    assert 0 <= y <= 1
    upper = sum((-y)**j / factorial(j) for j in range(31))
    lo, hi = round_outward(upper - y**31/factorial(31), upper)
    assert lo > 0
    return round_outward(lo**64, hi**64)


def cos_at(x, pi_bounds):
    """Enclose cos(x), using paired Machin bounds for the argument reduction."""
    lo_pi, hi_pi = pi_bounds
    pi_mid = (lo_pi + hi_pi)/2
    turns = round(x/(2*pi_mid))
    angle = x - 2*turns*pi_mid
    assert abs(angle) < 4
    poly = sum((-1)**j * angle**(2*j)/factorial(2*j) for j in range(23))
    # Degree 45 Taylor polynomial; perturbing the angle costs at most |d angle|.
    error = F(4**46, factorial(46)) + abs(turns)*(hi_pi - lo_pi)
    return round_outward(poly - error, poly + error)


def centered_sum(h, t, envelope=False):
    """Enclose .5 plus the finite witness sum, or .5 minus the total amplitude."""
    lower = upper = F(1, 2)
    pi_bounds = pi_bracket()
    for center in CENTERS:
        a, b = exp_minus(h*center**2)
        if envelope:
            lower -= 2*b
            upper -= 2*a
        else:
            c, d = cos_at(t*center, pi_bounds)
            products = (a*c, a*d, b*c, b*d)
            lower += 2*min(products)
            upper += 2*max(products)
    # Each true ordinate is within RADIUS. Bound its summand's derivative.
    data_error = len(CENTERS)*2*(2*h*32 + abs(t))*RADIUS
    # The beta completion identity implies sum m/(9/4+gamma^2) < 1.
    # (9/4+u^2) exp(-hu^2) decreases for u >= 32 at both h values.
    weighted_tail = (F(9, 4) + 32**2) * exp_minus(h * 32**2)[1]
    return lower - data_error - 2*weighted_tail, upper + data_error + 2*weighted_tail


def show_bounds(label, interval):
    lo, hi = interval
    # Printed integers give outward rational endpoints, in units of 10^-15.
    scale = 10**15
    print(f"{label}: [{(lo*scale).__floor__()}, {(hi*scale).__ceil__()}] / 10^15")


def verify_derivative_bounds():
    """Uniform first-harmonic derivative control on 0.040 <= h <= 0.041."""
    low, high = F("0.040"), F("0.041")
    finite = sum((g + RADIUS)**2 * exp_minus(low * (g - RADIUS)**2)[1]
                 for g in CENTERS[1:])
    y = 32**2
    tail = y * (F(9, 4) + y) * exp_minus(low * y)[1]
    g = CENTERS[0]
    first = (g - RADIUS)**2 * exp_minus(high * (g + RADIUS)**2)[0]
    assert finite + tail < 2 and first > 7
    print("On [0.040, 0.041], the higher-harmonic second moment is < 2")
    print("and the first-harmonic second moment is > 7.")


def main():
    witness = centered_sum(H_LOW, WITNESS)
    global_lower_envelope = centered_sum(H_HIGH, F(0), envelope=True)
    show_bounds("At h = 0.04007656562, witness value", witness)
    show_bounds("At h = 0.04007656609, 1/2 minus total amplitude", global_lower_envelope)
    assert witness[1] < -F(74977, 10**15)
    assert global_lower_envelope[0] > F(47190, 10**15)
    assert H_HIGH - H_LOW == F(47, 10**11)
    print("Certified strict bracket: 0.04007656562 < h_* < 0.04007656609")
    verify_derivative_bounds()


if __name__ == "__main__":
    main()
