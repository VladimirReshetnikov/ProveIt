#!/usr/bin/env python3
"""Exact rational certificates for the improved high-order Gowers norm rate.

This checks finite parameter choices and numerical bounds.  The uniform
mathematical result is proved in gowers_spectral_uniformity_affine.tex, not by this program.
No third-party packages are needed.  All logarithms and exponentials used for
certification are enclosed by rational series bounds with directed rounding.
"""

import argparse
import json
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path

PRECISION = 100
DEN = 10 ** PRECISION
LOG_TERMS = 128


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def floor(q):
    return q.numerator // q.denominator


def ceil(q):
    return -((-q.numerator) // q.denominator)


def round_out(lo, hi):
    return F(floor(lo * DEN), DEN), F(ceil(hi * DEN), DEN)


def local_log(q):
    """Enclose log(q) for 1 <= q <= 2 using the atanh expansion."""
    require(1 <= q <= 2, 'local logarithm outside [1,2]')
    z = (q - 1) / (q + 1)
    z2 = z * z
    power = z
    total = F(0)
    for j in range(LOG_TERMS):
        total += power / (2 * j + 1)
        power *= z2
    lo = 2 * total
    remainder = 2 * power / ((2 * LOG_TERMS + 1) * (1 - z2))
    return round_out(lo, lo + remainder)


@lru_cache(maxsize=None)
def log_bounds(q):
    q = F(q)
    require(q > 0, 'nonpositive logarithm argument')
    r = q.numerator.bit_length() - q.denominator.bit_length()
    scale = F(2 ** r) if r >= 0 else F(1, 2 ** (-r))
    if q < scale:
        r -= 1
        scale /= 2
    if q >= 2 * scale:
        r += 1
        scale *= 2
    y = q / scale
    lo, hi = local_log(y)
    l2, u2 = local_log(F(2))
    if r >= 0:
        return round_out(lo + r * l2, hi + r * u2)
    return round_out(lo + r * u2, hi + r * l2)


def exp_upper(q):
    require(q >= 0, 'negative exponential argument')
    M = 64
    require(q < M + 1, 'exponential argument too large for tail bound')
    term = F(1)
    total = term
    for j in range(1, M):
        term *= q / j
        total += term
    next_term = term * q / M
    upper = total + next_term / (1 - q / (M + 1))
    return F(ceil(upper * DEN), DEN)


def decimal_upper(q, digits):
    scale = 10 ** digits
    scaled = ceil(q * scale)
    return f'{scaled // scale}.{scaled % scale:0{digits}d}'


def verify_case(d):
    require(d % 2 == 0, 'the displayed family uses even d')
    n = 2 ** d
    root = 2 ** (d // 2)
    tau = F(3 * d + 10, root)
    kap = F(5, root)
    require(0 < tau <= F(1, 2) and 0 < kap < F(1, 2), 'invalid tail parameters')
    k = ceil(8 / tau)
    rho = kap / 2

    # log(4/(kappa*beta)) = log(4/kappa) +
    #              k*(log(8/rho) + log(2k)/2).
    logterm_upper = log_bounds(4 / kap)[1]
    logterm_upper += k * (log_bounds(8 / rho)[1] + log_bounds(F(2 * k))[1] / 2)
    L = ceil(8 * k / (rho * rho) * logterm_upper)
    require(n // 4 >= k + 1, 'Fourier tail degree condition failed')
    a = F(k * (d + 1), n)
    require(0 < a < 1, 'optimized cube parameter outside range')

    # A lower bound for the left-minus-right positivity condition.
    require(F(n, 2) - k > 0, 'positivity coefficient not positive')
    margin_lower = (F(n, 2) - k) * log_bounds(1 / a)[0]
    margin_lower -= k * log_bounds(256 * L * (1 + a))[1]
    margin_lower -= log_bounds(F(2))[1]
    require(margin_lower > 0, 'cube positivity condition failed')

    E_upper = log_bounds(1 + a)[1]
    E_upper += a * log_bounds(256 * L * (1 + a) / a)[1]
    E_upper += F(k * (d - 1), n) * log_bounds(F(d - 1))[1]
    E_upper += F(2, n) * log_bounds(F(2))[1]
    E_upper = F(ceil(E_upper * DEN), DEN)
    factor_upper = exp_upper(4 * E_upper) / (1 - kap) ** 4
    excess_upper = (factor_upper - 1) / 3 + 2 * tau
    upper = F(1, 3) + excess_upper
    require(upper >= F(1, 3), 'bad endpoint normalization')

    return {
        'd': d,
        'tau': str(tau),
        'kappa': str(kap),
        'k': k,
        'L': str(L),
        'a': str(a),
        'E_upper': decimal_upper(E_upper, 32),
        'positivity_margin_lower_integer': floor(margin_lower),
        'c_d_upper': decimal_upper(upper, 24),
        'excess_above_one_third_upper': decimal_upper(excess_upper, 32),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = [verify_case(d) for d in (24, 28, 32, 40, 48, 64, 80, 128)]
    report = {
        'status': 'all rational enclosure and parameter checks passed',
        'arithmetic': 'integers and fractions only',
        'precision_decimal_places': PRECISION,
        'log_terms': LOG_TERMS,
        'parameter_rule': 'tau=(3d+10)/2^(d/2), kappa=5/2^(d/2)',
        'cases': cases,
    }
    result = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(result, encoding='utf-8')
    print(result)


if __name__ == '__main__':
    main()
