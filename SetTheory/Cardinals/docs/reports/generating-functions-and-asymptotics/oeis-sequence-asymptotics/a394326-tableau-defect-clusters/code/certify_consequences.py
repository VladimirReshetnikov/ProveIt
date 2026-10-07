#!/usr/bin/env python3
"""Exact rational remainder, non-golden, monotonicity and inverse checks."""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
from rigorous import A, E, fold, states, require


def interval_fractions(data):
    scale = 1 << data['scale_bits']
    return F(int(data['lo']), scale), F(int(data['hi']), scale)


def remainder_certificate(global_result, local_result):
    require(global_result['status'] == local_result['status'] == 'PASS', 'upstream certificate failed')
    schur = global_result['Schur']
    r = F(global_result['z_majorant_radius'])
    kappa = F(schur['inverse_strict_upper'])
    b, c, t = (F(schur[k]) for k in ('B_strict_upper', 'C_strict_upper', 'D_strict_upper'))
    delta = b*c/(1-t)
    eta = kappa*delta
    require(eta < 1, 'global Schur contraction failed')
    core = kappa/(1-eta)*(1+b/(1-t))
    tail = (1+c*core)/(1-t)
    require(max(core, tail) < 525, 'full resolvent bound failed')
    kaa = sum(F(v)*r**e for (u, e), v in fold(A).items() if u == A)
    kao = sum(F(v)*r**e for (u, e), v in fold(A).items() if u != A)
    g = F(0)
    for u in states(4, 'K'):
        if u == A:
            continue
        value = sum(F(v)*r**e for (w, e), v in fold(u).items() if w == A)
        if u == E:
            value += r**3*(1+kaa)
        g = max(g, value)
    # Height changes by at most three; no state above height four reaches A.
    for u in states(12, 'K'):
        if sum(u) > 4:
            require(not any(v == A for v, _ in fold(u)), 'unexpected far entry into A')
    require(kaa < F(105, 100) and kao < F(276, 100) and g < F(159, 100),
            'row-polynomial majorants failed')
    c_bound = F(105, 100)+F(276, 100)*525*F(159, 100)
    require(c_bound < 2400, 'generating function circle bound failed')
    rho_upper = F(local_result['real']['rho_interval_exact'][1])
    amplitude_upper = interval_fractions(local_result['residue']['asymptotic_amplitude'])[1]
    require(rho_upper < F(619, 1000) and amplitude_upper < F(184, 1000),
            'principal-pole bound inputs exceeded')
    radius = F(global_result['q_circle_radius'])
    principal = F(184, 1000)*F(619, 1000)/(radius-F(619, 1000))
    require(2400+principal < 2500, 'published coefficient remainder failed')
    return {'status': 'PASS', 'resolvent_strict_upper': '525',
            'core_strict_upper': str(core), 'tail_strict_upper': str(tail),
            'Kaa_majorant': str(kaa), 'Kao_majorant': str(kao), 'g_majorant': str(g),
            'C_circle_strict_upper': '2400', 'principal_circle_strict_upper': str(principal),
            'remainder_constant': '2500', 'remainder_radius': str(radius),
            'scope': 'For every integer n>=0, |a_n-c*rho^(-n)| <=2500*(100/63)^n.'}


def generalized_binomial(a, k):
    result = F(1)
    for j in range(k):
        result *= (a-j)/(j+1)
    return result


def multiply(a, b, order):
    out = [F(0)]*(order+1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j <= order:
                out[i+j] += x*y
    return out


def power_one_plus(w, exponent, order):
    result, power = [F(0)]*(order+1), [F(1)]+[F(0)]*order
    for j in range(order+1):
        coefficient = generalized_binomial(exponent, j)
        result = [a+coefficient*b for a, b in zip(result, power)]
        power = multiply(power, w, order)
    return result


def check_inverse_series(order=8):
    """Check the all-order formula at exact rational alpha by formal reversion.

    The theorem's general formula is proved analytically in the report. These
    finite algebraic checks exercise signs, normalization and indexing without
    evaluating non-rigorous logarithms or rounding a threshold near an integer.
    """
    cases = []
    for alpha in (F(1, 7), F(2, 5), F(3, 4), F(9, 10)):
        for epsilon in (-1, 1):
            w = [F(0)]*(order+1)
            # w=epsilon*mu*(1+w)^alpha is contractive in the formal mu-adic sense.
            for _ in range(order):
                p = power_one_plus(w, alpha, order)
                w = [F(0)]+[epsilon*x for x in p[:order]]
            log_v, power = [F(0)]*(order+1), w[:]
            for j in range(1, order+1):
                log_v = [a+F((-1)**(j+1), j)*b for a, b in zip(log_v, power)]
                power = multiply(power, w, order)
            target = [F(0)]+[F(epsilon**k, k)*generalized_binomial(alpha*k-1, k-1)
                            for k in range(1, order+1)]
            require(log_v == target, 'Lagrange envelope coefficients disagree')
            cases.append({'alpha': str(alpha), 'epsilon': epsilon,
                          'log_v_coefficients_mu_1_through_8': [str(x) for x in log_v[1:]]})
    return {'order': order, 'exact_rational_alpha_cases': cases,
            'scope': 'Algebraic verification of the two envelope series, not of a single-ceiling approximation.'}


def inverse_certificate(local_result, remainder):
    rho_low, rho_high = (F(x) for x in local_result['real']['rho_interval_exact'])
    c_low, c_high = F('0.1838102868'), F('0.1838120734')
    actual_low, actual_high = interval_fractions(local_result['residue']['asymptotic_amplitude'])
    require(c_low < actual_low <= actual_high < c_high, 'amplitude endpoints do not contain certificate')
    radius = F(remainder['remainder_radius'])
    maximum = F(remainder['remainder_constant'])
    x = F('0.618034')
    require(x*x+x-1 == F(6289, 250000000000) and x < rho_low,
            'golden-ratio exclusion failed')
    require(F('1.6180188314') < 1/rho_high < 1/rho_low < F('1.6180189139'),
            'growth constant enclosure failed')
    delta_low, delta_high = 1-rho_high-rho_high**2, 1-rho_low-rho_low**2
    require(F('-0.00001295') < delta_low < delta_high < F('-0.00001287'),
            'signed Fibonacci residual enclosure failed')
    n = 600
    relative_error = maximum/c_low*(rho_high/radius)**n
    lhs, rhs = relative_error*(1+1/radius), 1/rho_high-1
    require(relative_error < F(138, 1000) < 1, 'positivity threshold failed')
    require(lhs < F(356406, 1000000) < rhs, 'strict-increase threshold failed')
    y = c_high*rho_low**(-n)+maximum*radius**(-n)
    y0 = -((-y.numerator)//y.denominator)
    require(F(y0-1) < y <= F(y0), 'incorrect exact prefix-bound ceiling')
    return {'status': 'PASS', 'rho_lower': str(rho_low), 'rho_upper': str(rho_high),
            'amplitude_lower': str(c_low), 'amplitude_upper': str(c_high),
            'growth_constant_widened_interval': ['1.6180188314', '1.6180189139'],
            'golden_test_positive_value': str(x*x+x-1),
            'signed_Fibonacci_residual_interval_widened': ['-0.00001295', '-0.00001287'],
            'positivity_and_strict_increase_from_n': n,
            'relative_error_bound_at_600_strict_upper': '0.138',
            'monotonicity_left_strict_upper': '0.356406',
            'monotonicity_right_exact': str(rhs),
            'threshold_Y0_exact_integer': str(y0), 'threshold_Y0_digits': len(str(y0)),
            'envelope_inverse_series': check_inverse_series(),
            'scope': 'For y>Y0 the threshold inverse is enclosed between the two ceilings of the exact monotone envelope roots, both greater than 600.'}


def main():
    from certify_rational_circle import run as global_run
    from certify_local import run as local_run
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    global_result, local_result = global_run(args.data_dir), local_run(args.data_dir)
    remainder = remainder_certificate(global_result, local_result)
    result = {'status': 'PASS', 'remainder': remainder,
              'inverse': inverse_certificate(local_result, remainder)}
    text = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
