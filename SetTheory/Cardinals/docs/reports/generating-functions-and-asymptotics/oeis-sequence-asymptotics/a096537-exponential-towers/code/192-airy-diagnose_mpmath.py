#!/usr/bin/env python3
"""Optional mpmath diagnostics only: not certified intervals or proof tests.

This module is never imported by the mandatory mathematical checker, build,
manifest verifier, replay command, or synthetic build-guard suite.
"""
from __future__ import annotations
import argparse
import json
import sys


def need(condition, message):
    if not condition:
        raise ValueError(message)


def log_height(mp, height, scale):
    """Stable finite exact-height tower evaluated numerically at x=scale/height."""
    child_log = mp.mpc(0)
    difference = mp.mpc(scale)
    log_difference = mp.log(scale)
    def log_exprel(z):
        return mp.log(mp.expm1(z)/z) if z else mp.mpc(0)
    for i in range(height-1, 0, -1):
        z = scale * mp.mpf(i) / height
        factor_log = mp.log(z) + child_log + log_exprel(difference)
        log_difference += factor_log
        difference *= mp.exp(factor_log)
        child_log = z * mp.exp(child_log)
    return log_difference + child_log + log_exprel(difference)


def run(heights, digits):
    need(type(digits) is int and 30 <= digits <= 200, 'precision must be 30..200')
    need(type(heights) is list and 1 <= len(heights) <= 5 and all(type(h) is int and 10 <= h <= 100000 for h in heights), 'one to five heights in 10..100000 required')
    try:
        import mpmath as mp
    except ImportError as exc:
        raise ValueError('Optional diagnostic requires mpmath; core checks do not') from exc
    mp.mp.dps = digits
    rho = 1 - 1/mp.e
    alpha = mp.e - 1
    a = mp.power(2, -mp.mpf(1)/3)
    ai0 = mp.airyai(0)
    K = mp.power(2, mp.mpf(1)/6) * mp.sqrt(mp.e/mp.pi) / ai0**2
    def real(value):
        return mp.nstr(mp.re(value), digits-5)
    def complex_pair(value):
        return [real(value), mp.nstr(mp.im(value), digits-5)]
    rows = []
    for height in heights:
        m = mp.root(height, 3)
        base = log_height(mp, height, 1/mp.e)
        tilts, characteristic = [], []
        for tilt in (mp.mpf(-1), -mp.mpf(1)/4, mp.mpf(1)/4, mp.mpf(1)):
            actual = log_height(mp, height, (1+tilt/m**2)/mp.e)
            predicted = (mp.log(mp.power(2, mp.mpf(1)/6)*mp.sqrt(mp.e/mp.pi)
                               / mp.airyai(-a*tilt)**2) + mp.log(height)/6
                         - alpha*height + alpha*tilt*m)
            tilts.append({'lambda': real(tilt), 'ratio_to_limit': real(mp.exp(actual-predicted))})
        for t in (mp.mpf(1)/2, mp.mpf(1), mp.mpf(2)):
            theta = t/m**2
            actual = mp.exp(log_height(mp, height, mp.exp(1j*theta)/mp.e)
                            - base - 1j*theta*alpha*height)
            predicted = ai0**2/mp.airyai(-a*1j*t)**2
            characteristic.append({'t': real(t), 'finite': complex_pair(actual),
                                   'limit': complex_pair(predicted),
                                   'absolute_difference': real(abs(actual-predicted))})
        rows.append({'height': height,
                     'critical_ratio_to_limit': real(mp.exp(base+alpha*height-mp.log(height)/6)/K),
                     'tilts': tilts, 'characteristic': characteristic})
    return {'status': 'DIAGNOSTIC_ONLY', 'certifies_any_interval': False,
            'proves_asymptotic_claims': False, 'decimal_working_precision': digits,
            'mpmath_version': mp.__version__,
            'constants': {'K': real(K), 'rho': real(rho),
                          'normalized_coefficient_amplitude': real(mp.sqrt(2/(mp.pi*rho)))},
            'rows': rows,
            'scope': 'Uncertified floating-point illustrations; no interval bounds, fitted '
                     'constants, certified digits, remainder estimates, or effective onset.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--heights', nargs='+', type=int, default=[100, 1000])
    parser.add_argument('--digits', type=int, default=50)
    args = parser.parse_args()
    try:
        print(json.dumps(run(args.heights, args.digits), sort_keys=True, indent=2, allow_nan=False))
    except (ValueError, TypeError, ArithmeticError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
