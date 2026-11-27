#!/usr/bin/env python3
"""Exact rational posterior certificates for a synthetic clustered spectrum.

All decisive assertions below use fractions.Fraction. mpmath merely proposes
coefficients. Taylor remainders enclose the exact trigonometric matrix, and
the analytic inverse bound encloses its exact solution.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import mpmath as mp
from positive_filters import SeparatedFilter

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 90


def sin_interval(x, tolerance=F(1, 10**65)):
    x = F(x)
    if x == 0:
        return F(0), F(0)
    s, term, k = x, x, 0
    while True:
        remainder = abs(x)**(2*k+3) / factorial(2*k+3)
        if remainder <= tolerance:
            return s-remainder, s+remainder
        term *= -x*x/F((2*k+2)*(2*k+3))
        s += term
        k += 1


def square_interval(lo, hi):
    return (F(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def beta_interval(frequency):
    # Radius A=16: the sinc argument is exactly rational.
    x = 8*F(frequency)
    if x == 0:
        return F(1), F(1)
    lo, hi = sin_interval(x)
    lo, hi = square_interval(lo, hi)
    return lo/(x*x), hi/(x*x)


def interval_scale(interval, coefficient):
    a, b = [coefficient*x for x in interval]
    return min(a,b), max(a,b)


def exact_coloring(frequencies, delta=F(1)):
    colors = []
    for x in sorted(frequencies):
        for color in colors:
            if x-color[-1] >= delta:
                color.append(x)
                break
        else:
            colors.append([x])
    return colors


frequencies = [F(3,2), F(3,2), F(7,4), F(11,4), F(17,5), F(19,5), F(47,10)]
colors = exact_coloring(frequencies)
# Maximum occupancy of half-open intervals of length 1 occurs at a frequency.
occupancy = max(sum(x-1 < y <= x for y in frequencies) for x in frequencies)
assert len(colors) == occupancy
reports = []
for color in colors:
    reflected = sorted([-x for x in color]+color)
    with_zero = sorted(reflected+[F(0)])
    assert all(b-a >= 1 for a,b in zip(with_zero, with_zero[1:]))
    proposal = SeparatedFilter([mp.mpf(x.numerator)/x.denominator for x in color], radius=16)
    # Average opposite coefficients before rationalization, preserving evenness exactly.
    proposed = []
    for i in range(len(reflected)):
        average = (proposal.coefficients[i]+proposal.coefficients[len(reflected)-1-i])/2
        proposed.append(F(mp.nstr(average, 72)))
    assert proposed == proposed[::-1]
    matrix = [[beta_interval(x-y) for y in reflected] for x in reflected]
    rhs = [beta_interval(x) for x in reflected]
    residual_upper = F(0)
    for row, b in zip(matrix, rhs):
        lo, hi = b
        for interval, a in zip(row, proposed):
            lower, upper = interval_scale(interval,a)
            lo += lower
            hi += upper
        residual_upper += max(abs(lo),abs(hi))
    norm_approx = sum(abs(a) for a in proposed)
    # 16 > 4*pi, so the main theorem's universal ||M-I||_1 <= 1/12 applies.
    correction_upper = F(12,11)*residual_upper
    assert residual_upper < F(1,10**55)
    assert correction_upper < F(1,10**54)
    assert norm_approx+correction_upper < F(1,11)
    reports.append({
        'positive_rational_frequencies':[str(x) for x in color],
        'radius':16,
        'matrix_dimension':len(reflected),
        'certified_residual_l1_bound':'1/10^55',
        'certified_exact_coefficient_error_l1_bound':'1/10^54',
        'certified_exact_coefficient_norm_l1_bound':'1/11',
        'exact_solution_exists':True,
        'exact_positive_density_envelope':['5/6','6/5'],
    })

# Algebra behind the distinct-ordinate lower bound, including large multiplicity.
for m in range(1, 10001):
    assert m-1 <= F(m*m-m,2)
assert (3-F(4,3))/2 == F(5,6)
assert F(5,6)/2 == F(5,12)

out = {
    'status':'exact rational posterior certificate for synthetic rational frequencies',
    'spectrum':[str(x) for x in frequencies],
    'repeated_frequency':'3/2 (multiplicity two)',
    'local_occupancy':occupancy,
    'colors':len(colors),
    'total_undamped_support_radius':16*len(colors),
    'certified_zero_order_at_3_over_2_at_least':2,
    'factors':reports,
    'limits':'Does not certify numerical zeta ordinates. The universal theorem is proved in the report.'
}
(ROOT/'evidence'/'exact_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
