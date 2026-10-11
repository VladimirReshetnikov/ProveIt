#!/usr/bin/env python3
"""Reproduce the bicolored parity identities and their exact finite algebra.

The analytical proof is bicolored_parity.tex. Exact polynomial checks below
check the rational partial-fraction implementation, and the source-expression
simplification uses Fraction. Numerical comparisons use the independent
Mellin integral for the defining double values; they are diagnostics, not
interval certificates or a substitute for the analytical proof.

Requires mpmath. Usage: python verify_bicolored_parity.py [report.json]
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
import sys
import mpmath as mp


def polynomial_checks():
    """Multiply the k=1 partial fractions by t**q*(t+1)**p."""
    count = 0
    for p in range(1, 8):
        for q in range(1, 8):
            w = p + q
            coefficients = [0] * w
            for j in range(1, q + 1):
                a = (-1)**(q-j) * comb(w-j-1, p-1)
                for degree in range(p+1):
                    coefficients[q-j+degree] += a * comb(p, degree)
            for j in range(1, p + 1):
                b = (-1)**q * comb(w-j-1, q-1)
                for degree in range(p-j+1):
                    coefficients[q+degree] += b * comb(p-j, degree)
            assert coefficients == [1] + [0] * (w-1)
            count += 1
    return count


def source_algebra():
    # Coordinates: zeta(3), pi*G, pi**2*log(2), log(2)**3.
    terms = [
        [F(3), F(0), F(0), F(0)],
        [F(0), F(0), -4*F(5, 96), 4*F(1, 8)],
        [F(0), F(-1), F(1, 8), F(0)],
        [F(0), F(0), 4*F(1, 32), -4*F(1, 8)],
        [-3*F(29, 32), 3*F(1, 4), 3*F(1, 96), F(0)],
    ]
    found = [sum(t[j] for t in terms) for j in range(4)]
    assert found == [F(9,32), F(-1,4), F(7,96), F(0)]
    return [str(x) for x in found]


def double_value(p, q, x, y):
    def integrand(t):
        return (-mp.log(t))**(p-1) * x * mp.polylog(q, x*y*t)/(1-x*t)
    return mp.quad(integrand, [0, mp.mpf('0.5'), 1])/mp.factorial(p-1)


def bilateral_single(j, x):
    if abs(x-1) < mp.mpf('1e-45'):
        return 2*mp.zeta(j) if j % 2 == 0 else mp.mpf(0)
    return mp.polylog(j, x) + (-1)**j * mp.polylog(j, 1/x)


def parity_rhs(p, q, x, y):
    w = p+q
    r = x*y
    value = mp.fsum(
        (-1)**j*comb(w-j-1, p-1)*bilateral_single(j, r)*mp.polylog(w-j, x)
        for j in range(1, q+1))
    value += mp.fsum(
        comb(w-j-1, q-1)*bilateral_single(j, r)*mp.polylog(w-j, 1/y)
        for j in range(1, p+1))
    value -= (comb(w-1, p)*mp.polylog(w, 1/y)
              + comb(w-1, q)*mp.polylog(w, x)
              + bilateral_single(p, x)*mp.polylog(q, 1/y))
    return (-1)**q*value + (-1)**w*mp.polylog(w, 1/r)


def moment_checks():
    records = []
    for m in range(1, 7):
        w = 2*m+1
        right = (mp.mpf(1)/2 * (1-mp.mpf(2)**(-2*m))
                 * (1-mp.mpf(w)/2**w) * mp.zeta(w))
        right -= mp.fsum(
            (1-mp.mpf(2)**(1-2*k)) * (1-mp.mpf(2)**(1-w+2*k))
            / mp.mpf(2)**(w-2*k) * mp.zeta(2*k) * mp.zeta(w-2*k)
            for k in range(1,m))
        right -= (mp.mpf(1)/2 * (1-mp.mpf(2)**(1-2*m))
                  * (1-mp.mpf(2)**(-2*m)) * mp.zeta(2*m)*mp.log(2))
        left = mp.quad(lambda t: t*(-mp.log(t))**(2*m-1)*mp.log(1+t)
                       /(1+t*t), [0, mp.mpf('0.5'), 1])/mp.factorial(2*m-1)
        error = abs(left-right)
        assert error < mp.mpf('1e-44')
        records.append({'m': m, 'integral': mp.nstr(left,45),
                        'absolute_error': mp.nstr(error,12)})
    return records


def main():
    mp.mp.dps = 50
    pairs = [
        ('i,i', mp.j, mp.j), ('-1,i', -1, mp.j),
        ('i,-1', mp.j, -1), ('i,-i', mp.j, -mp.j),
        ('third_root,third_root', mp.exp(2*mp.pi*mp.j/3),
         mp.exp(2*mp.pi*mp.j/3)),
        ('noncyclotomic', mp.exp(mp.mpf('.72')*mp.j),
         mp.exp(-mp.mpf('1.11')*mp.j)),
    ]
    records = []
    max_error = mp.mpf(0)
    for p, q in [(1,1), (1,2), (2,1), (2,2), (1,4), (3,2), (4,3), (3,4)]:
        for name, x, y in pairs:
            x, y = mp.mpc(x), mp.mpc(y)
            value = double_value(p, q, x, y)
            left = value - (-1)**(p+q)*mp.conj(value)
            error = abs(left-parity_rhs(p, q, x, y))
            max_error = max(max_error, error)
            assert error < mp.mpf('1e-44'), (p, q, name, error)
            records.append({'p': p, 'q': q, 'colors': name,
                            'absolute_error': mp.nstr(error, 12)})
    L, P, G = mp.log(2), mp.pi, mp.catalan
    beta = lambda n: (mp.zeta(n, mp.mpf(1)/4)-mp.zeta(n, mp.mpf(3)/4))/4**n
    formulas = [
        ('source_family2_short', 1, 2, mp.j, mp.j,
         9*mp.zeta(3)/32-P*G/4+7*P**2*L/96),
        ('mixed_weight3', 1, 2, -1, mp.j,
         15*mp.zeta(3)/16-P*G/2+P**2*L/48),
        ('mixed_weight4', 1, 3, -1, mp.j,
         3*P**3*L/32-3*beta(4)+21*P*mp.zeta(3)/64),
        ('mixed_weight5', 1, 4, -1, mp.j,
         7*P**4*L/11520-P*beta(4)/2+P**2*mp.zeta(3)/32+135*mp.zeta(5)/128),
        ('mixed_weight6', 1, 5, -1, mp.j,
         5*P**5*L/512-5*beta(6)+465*P*mp.zeta(5)/1024+3*P**3*mp.zeta(3)/64),
    ]
    explicit = []
    for name, p, q, x, y, right in formulas:
        x, y = mp.mpc(x), mp.mpc(y)
        difference = double_value(p,q,x,y)-double_value(q,p,y,x)
        left = mp.re(difference) if (p+q)%2 else mp.im(difference)
        error = abs(left-right)
        assert error < mp.mpf('1e-44')
        explicit.append({'identity': name, 'left': mp.nstr(left, 45),
                         'absolute_error': mp.nstr(error, 12)})
    v = (1+mp.j)/2
    original_right = (3*mp.zeta(3)-4*L*mp.re(mp.polylog(2,v))
                      -P*mp.im(mp.polylog(2,v))
                      -4*L*mp.re(double_value(1,1,mp.j,1))
                      +3*mp.re(double_value(1,2,mp.j,1)))
    short = mp.mpf(9)*mp.zeta(3)/32-P*G/4+7*P**2*L/96
    original_error = abs(original_right-short)
    assert original_error < mp.mpf('1e-44')
    report = {
        'status': 'all checks passed', 'working_decimal_digits': mp.mp.dps,
        'exact_partial_fraction_polynomial_checks': polynomial_checks(),
        'exact_source_simplification_coefficients': source_algebra(),
        'parity_integral_comparisons': records,
        'maximum_parity_absolute_error': mp.nstr(max_error, 14),
        'explicit_identity_comparisons': explicit,
        'original_family2_right_side_error': mp.nstr(original_error, 14),
        'all_weight_moment_checks': moment_checks(),
        'evidence_boundary': ('Exact finite algebra plus independent floating-point '
                             'Mellin diagnostics. The all-weight proof is analytical; '
                             'these numerical results are not interval certificates.'),
    }
    output = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1] / 'verification/bicolored_parity.json'
    output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: report[key] for key in [
        'status', 'working_decimal_digits', 'exact_partial_fraction_polynomial_checks',
        'maximum_parity_absolute_error', 'original_family2_right_side_error']}, indent=2))


if __name__ == '__main__':
    main()
