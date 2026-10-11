#!/usr/bin/env python3
"""Independent continued-Mellin diagnostics for harmonic Laurent data.

Requires Python 3 and mpmath.  No b_k(u,a), two-variable generating function,
reciprocal-Gamma Taylor coefficient, or symbolic Laurent theorem is used to
evaluate E_r.  The evaluator continues the ONE-variable defining Mellin
integral by integrating the convergent local logarithmic series on (0,delta)
term by term, and performs numerical quadrature on (delta,infinity).

The predicted Laurent polynomials below are hard-coded displayed formulas.
Agreement of N=80 and N=100 and the observed O(epsilon) remainder are numerical
diagnostics, NOT certified error bounds and NOT a substitute for the proof.
The script writes a JSON record beside itself.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp


mp.mp.dps = 110
DELTA = mp.mpf('0.5')


def convolve(x, y, degree):
    return [mp.fsum(x[j]*y[k-j] for j in range(k+1))
            for k in range(degree+1)]


def local_kernel_coefficients(r, a, degree):
    """Rows c[j][k] in K_r(t)=sum_jk c[j][k] t^(k-1)(-log t)^j.

    Direct scalar factorization of the Mellin kernel:
      K_r(t) = t^(-1) q_a(t) (-log(t)+ell(t))^r/r!,
      q_a(t) = exp(-a*t)*t/(exp(t)-1),
      ell(t) = -log((1-exp(-t))/t).
    q is obtained from the Bernoulli generating function; ell is its scalar
    logarithmic series.  Both local series have radius 2*pi.
    """
    base = [mp.bernoulli(k)/mp.factorial(k) for k in range(degree+1)]
    exponential = [(-a)**k/mp.factorial(k) for k in range(degree+1)]
    q = convolve(base, exponential, degree)
    ell = [mp.mpf(0)]*(degree+1)
    ell[1] = mp.mpf('0.5')
    for k in range(2, degree+1, 2):
        ell[k] = -mp.bernoulli(k)/(k*mp.factorial(k))
    powers = [[mp.mpf(1)]+[mp.mpf(0)]*degree]
    for power in range(1, r+1):
        powers.append(convolve(powers[-1], ell, degree))
    rows = []
    for j in range(r+1):
        row = convolve(q, powers[r-j], degree)
        scale = mp.factorial(j)*mp.factorial(r-j)
        rows.append([value/scale for value in row])
    return rows


def logarithmic_moment(z, j):
    """Meromorphic continuation of int_0^delta t^(z-1)(-log t)^j dt."""
    L = -mp.log(DELTA)
    return DELTA**z * mp.fsum(
        mp.factorial(j)/mp.factorial(j-k)*L**(j-k)/z**(k+1)
        for k in range(j+1))


def local_mellin(s, rows):
    return mp.fsum(coefficient*logarithmic_moment(s+k-1, j)
                   for j, row in enumerate(rows)
                   for k, coefficient in enumerate(row)
                   if coefficient)


def regular_mellin(s, r, a):
    def integrand(t):
        denominator = -mp.expm1(-t)
        logarithm = -mp.log(denominator)
        return (t**(s-1)*mp.exp(-(a+1)*t)/denominator
                *logarithm**r/mp.factorial(r))
    return mp.quad(integrand, [DELTA, 1, 3, 8, 20, mp.inf])


def stringify(value):
    return mp.nstr(value, 65)


def expected_laurent(r, m, a, epsilon):
    gamma, z2 = mp.euler, mp.zeta(2)
    if (r, m, a) == (1, 0, mp.mpf(0)):
        return -1/(2*epsilon)+(1-gamma)/2
    if (r, m, a) == (2, 1, mp.mpf(0)):
        return (-1/(12*epsilon**2)+(9-2*gamma)/(24*epsilon)
                +(-gamma**2+9*gamma+z2-10)/24)
    if (r, m, a) == (3, 2, mp.mpf(0)):
        return (1/(8*epsilon**2)+(6*gamma-17)/(48*epsilon)
                +(3*gamma**2-17*gamma-3*z2+17)/48)
    if r == 2 and m == 1 and a == mp.mpf(1)/3:
        return (-11/(36*epsilon**2)+(55-22*gamma)/(72*epsilon)
                +(-11*gamma**2+55*gamma+11*z2-42)/72)
    raise ValueError('No hard-coded prediction for this case')


def main():
    cases = [(1, 0, mp.mpf(0)), (2, 1, mp.mpf(0)),
             (3, 2, mp.mpf(0)), (2, 1, mp.mpf(1)/3)]
    epsilons = list(map(mp.mpf, ['0.0001', '0.00001', '0.000001']))
    record = {
        'method': ('One-variable continued Mellin integral; scalar local '
                   'logarithmic series on (0,1/2) plus quadrature on '
                   '(1/2,infinity); does not evaluate through the Laurent '
                   'coefficient theorem.'),
        'interpretation': ('Floating-point diagnostics only. Truncation '
                           'agreement is an empirical accuracy check, '
                           'not a rigorous error bound.'),
        'mpmath_version': mp.__version__,
        'decimal_precision': mp.mp.dps,
        'local_series_degrees': [80, 100],
        'split_point': stringify(DELTA),
        'baseline_checks': [],
        'laurent_checks': [],
    }
    for r, m, a in cases:
        print(f'Checking r={r}, m={m}, a={mp.nstr(a, 12)}', flush=True)
        rows80 = local_kernel_coefficients(r, a, 80)
        rows100 = local_kernel_coefficients(r, a, 100)
        if a == 0:
            # Calibrates the scalar continuation against a known absolutely
            # convergent value, E_r(2;0)=zeta(r+2).
            s = mp.mpf(2)
            actual = mp.rgamma(s)*(local_mellin(s, rows100)
                                    +regular_mellin(s, r, a))
            difference = actual-mp.zeta(r+2)
            assert abs(difference) < mp.mpf('1e-85')
            record['baseline_checks'].append({
                'r': r, 's': 2, 'a': '0',
                'expected': 'zeta(r+2)',
                'absolute_error': stringify(abs(difference)),
                'passed': True,
            })
        case = {'r': r, 'm': m, 'a': stringify(a), 'samples': []}
        scaled_remainders = []
        for epsilon in epsilons:
            s = -m+epsilon
            regular = regular_mellin(s, r, a)
            value80 = mp.rgamma(s)*(local_mellin(s, rows80)+regular)
            actual = mp.rgamma(s)*(local_mellin(s, rows100)+regular)
            numerical_change = abs(actual-value80)
            assert numerical_change < mp.mpf('1e-75')
            predicted = expected_laurent(r, m, a, epsilon)
            remainder = actual-predicted
            scaled_remainders.append(remainder/epsilon)
            case['samples'].append({
                'epsilon': stringify(epsilon),
                'continued_Mellin_value': stringify(actual),
                'predicted_principal_and_constant': stringify(predicted),
                'remainder': stringify(remainder),
                'remainder_divided_by_epsilon': stringify(remainder/epsilon),
                'absolute_change_from_degree_80_to_100': stringify(numerical_change),
            })
        # For a nonzero linear remainder coefficient, R(eps)/eps stabilizes;
        # this finite test does not purport to prove the O(eps) statement.
        drift = abs(scaled_remainders[-1]-scaled_remainders[-2])
        relative_drift = drift/max(mp.mpf(1), abs(scaled_remainders[-1]))
        passed = relative_drift < mp.mpf('0.0001')
        assert passed
        case['last_scaled_remainder_relative_drift'] = stringify(relative_drift)
        case['observed_linear_remainder'] = True
        record['laurent_checks'].append(case)
        print(f'  R(eps)/eps at eps=1e-6: '
              f'{mp.nstr(scaled_remainders[-1], 18)}', flush=True)
    record['all_diagnostics_passed'] = True
    destination = Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(f'Wrote {destination}', flush=True)


if __name__ == '__main__':
    main()
