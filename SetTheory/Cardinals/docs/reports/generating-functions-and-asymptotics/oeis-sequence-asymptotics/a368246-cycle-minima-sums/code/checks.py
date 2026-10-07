#!/usr/bin/env python3
"""Deterministic arithmetic certificate for Report234; valid also under python -O.

Print JSON to stdout, or write a new file outside the public source package.
The analytic theorem is proved in the article; this certificate does not infer
asymptotics from data and does not manufacture undisplayed sequence coefficients.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import factorial
from pathlib import Path
import hashlib
import sys

import mpmath as mp
import sympy as sp
from record_sum import (amplitudes, brute_counts, decimal_coefficients, emit,
                        finite_counts, gamma_root, inverse_model, model_values,
                        new_file_path, rational_coefficients, tree_log_coefficient)

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
HERE = Path(__file__).resolve().parent


def certificate():
    checks = []

    def verify(ok, label):
        if not ok:
            raise RuntimeError('certificate failed: ' + label)
        checks.append({'check': label, 'status': 'PASS'})

    listed = [1, 1, 0, 2, 3, 8, 90, 384, 2940, 18864, 232848, 1919520,
              23364000, 261282240, 3486637440, 48900116160, 746747164800,
              11559784320000, 201817271416320, 3580457619916800,
              68121866659875840, 1366946563510886400, 28802183294533017600,
              627950275273991577600]
    finite = finite_counts(60)
    rational = rational_coefficients(60)
    verify(finite[:len(listed)] == listed, 'OEIS initial values n=0..23')
    verify([1] + [rational[n - 1] * factorial(n - 1) for n in range(1, 61)] == finite,
           'independent integer finite and rational infinite products through n=60')
    brute = []
    for n in range(9):
        row = brute_counts(n)
        verify(row['records'] == row['cycle_minima'] == finite[n],
               'independent permutation enumeration n=%d' % n)
        brute.append(row)

    for degree in range(41):
        verify(tree_log_coefficient(1, degree) == int(degree == 0),
               'rooted-tree cancellation at z=1, degree=%d' % degree)
    jets = {}
    for q in range(2, 15):
        jet = [tree_log_coefficient(q, degree) for degree in range(41)]
        verify(all(value == 0 for value in jet[:q - 1]), 'root order %d onset' % q)
        verify(jet[q - 1] == Fraction(q ** (q - 2), factorial(q - 1)),
               'root order %d leading logarithm' % q)
        jets[str(q)] = [str(v) for v in jet]
    verify(tree_log_coefficient(2, 1) == 1 and tree_log_coefficient(2, 2) == -2,
           'B2(s)=s-2s^2+O(s^3)')
    verify(2 * tree_log_coefficient(4, 3) == Fraction(16, 3),
           'simple polynomial zero at i delays logarithm to -16 Q_i s^4 log(s)/3')

    t, ell = sp.symbols('t ell')
    s = t + t * t / 2
    logs = ell + t / 2
    local_log = -s * logs + s / 2 + 2 * s * s * logs
    local_f = sp.series(1 + local_log + local_log ** 2 / 2, t, 0, 3).removeO().expand()
    nonanalytic = sp.expand(local_f - local_f.subs(ell, 0))
    verify(sp.simplify(nonanalytic - (-t * ell + t ** 2 * (ell ** 2 / 2 + ell))) == 0,
           'exact -1 local nonanalytic jet in t=1+z')
    log2, zeta2 = sp.symbols('log2 zeta2')
    verify(sp.simplify((sp.Rational(3, 2) - log2) + (zeta2 - 1 - log2) - 1
                       + (2 * log2 + 1 - zeta2)) == sp.Rational(1, 2),
           'exact analytic s coefficient at -1 is 1/2')

    # Derive coefficient transfer from exact log and squared-log coefficients.
    # H below first denotes H_{m-1}; its expansion uses log(m)+gamma afterwards.
    x, H = sp.symbols('x H')
    m = 1 / x
    def ll(a):
        return 2 * (H - sum(1 / (m - r) for r in range(1, a + 1))) / (m - a)
    transfer = -1 / (m * (m - 1)) + (ll(0) - 2 * ll(1) + ll(2)) / 2
    transfer -= 2 / (m * (m - 1) * (m - 2))
    expansion = sp.series(transfer.subs(H, H - x / 2 - x * x / 12), x, 0, 4).removeO().expand()
    verify(sp.simplify(expansion - (-x * x + (2 * H - 6) * x ** 3)) == 0,
           'symbolic -1 transfer through m^-3')
    shifted = sp.series(-(-1 / (m - 1) ** 2 +
                         (2 * (H + sp.log(1 - x)) - 6) / (m - 1) ** 3),
                        x, 0, 4).removeO().expand()
    verify(sp.simplify(shifted - (x * x + (8 - 2 * H) * x ** 3)) == 0,
           'symbolic m=n-1 parity, logarithm and constant shift')
    for degree in (1, 2, 3):
        for index in range(degree + 1, 26):
            direct = -sum(Fraction((-1) ** j * int(sp.binomial(degree, j)), index - j)
                          for j in range(degree + 1))
            transferred = Fraction((-1) ** (degree + 1) * factorial(degree),
                                   __import__('math').prod(index - j for j in range(degree + 1)))
            verify(direct == transferred, 'exact t^%d log(t) transfer m=%d' % (degree, index))
    verify(-sp.Rational(3, 2) * (-2) == 3,
           'order-three complex root transfer coefficient is +3 C_omega')

    # Separate numerical evaluations at two precision levels. The analytic
    # truncation bounds are rigorous; mpmath roundoff is checked, not certified.
    numeric = amplitudes(80, 115)
    numeric_high = amplitudes(110, 115)
    with mp.workdps(80):
        verify(abs(gamma_root(2, mp.mpf(-1)) - 1) < mp.mpf('1e-70'),
               'Gamma product F(-1)=1')
        numerical_report = {}
        for key in ('C_omega', 'Q_i'):
            value, independent = numeric[key], numeric[key + '_polylog']
            bound = numeric[key + '_truncation_bound']
            difference = abs(value - independent)
            verify(difference <= bound + mp.mpf('1e-70'),
                   key + ' Gamma vs independent polylog within tail bound plus 1e-70 roundoff allowance')
            verify(abs(value - numeric_high[key]) < mp.mpf('1e-70'),
                   key + ' precision stability at 80 and 110 digits')
            verify(abs(independent - numeric_high[key + '_polylog']) < mp.mpf('1e-65'),
                   key + ' independent polylog precision stability')
            numerical_report[key] = {'real': mp.nstr(mp.re(value), 65),
                                      'imaginary': mp.nstr(mp.im(value), 65),
                                      'Gamma_polylog_difference': mp.nstr(difference, 24),
                                      'analytic_product_truncation_bound': mp.nstr(bound, 24)}
        verify(abs(numeric['Q_i']) > mp.mpf('0.1'), 'nonzero quotient at i')
        numerical_report['analytic_omitted_log_bound'] = mp.nstr(numeric['omitted_log_bound'], 24)
        numerical_report['polylog_cutoff'] = 115
        numerical_report['roundoff_limitation'] = 'mpmath arithmetic is not interval-certified; precision stability and explicit comparison tolerances are diagnostic checks.'

    lo, hi = decimal_coefficients(60, 35)
    verify(all(Fraction(lo[i]) <= rational[i] <= Fraction(hi[i]) for i in range(60)),
           'directed Decimal finite-coefficient bounds vs exact Fraction coefficients through n=60')
    decimal_report = {'digits': 35, 'nmax': 60,
                      'b60_lower': str(lo[-1]), 'b60_upper': str(hi[-1]),
                      'scope': 'Finite coefficient enclosure only, not an asymptotic error or threshold bound.'}

    inverses = []
    for order in (2, 3):
        result = inverse_model('1000', order, 80)
        with mp.workdps(80):
            root = mp.mpf(result['model_root'])
            b, derivative = model_values(root, order)
            residual = mp.loggamma(root) + mp.log(b) - 1000
            verify(abs(residual) < mp.mpf('1e-62'), 'finite K=%d Newton model residual' % order)
            verify(abs(derivative - mp.diff(lambda y: model_values(y, order)[0], root))
                   < mp.mpf('1e-65'), 'finite K=%d analytical derivative vs numerical differentiation' % order)
            independent_root = mp.findroot(lambda y: mp.loggamma(y) + mp.log(model_values(y, order)[0]) - 1000,
                                           (root - mp.mpf('.01'), root + mp.mpf('.01')))
            verify(abs(independent_root - root) < mp.mpf('1e-62'),
                   'finite K=%d Newton root vs secant evaluation' % order)
        finite_result = result['finite_order_construction']
        expected_steps = 2 if order == 2 else 3
        verify(finite_result['prescribed_undamped_steps'] == expected_steps
               and len(finite_result['iteration_history']) == expected_steps + 1,
               'finite K=%d construction uses exactly the prescribed undamped steps' % order)
        with mp.workdps(80):
            fixed = mp.mpf(finite_result['model_iterate'])
            ordinary = mp.mpf(result['iteration_history'][expected_steps]['x'])
            verify(abs(fixed - ordinary) < mp.mpf('1e-65'),
                   'finite K=%d undamped construction vs early converged-solver iterates' % order)
            verify(abs(mp.mpf(finite_result['log_residual'])) <
                   abs(mp.mpf(finite_result['iteration_history'][0]['log_residual'])),
                   'finite K=%d finite-step numerical residual improves from starter' % order)
        inverses.append(result)

    return {'report': 'Report234', 'sequence': 'A368246', 'status': 'PASS',
            'check_count': len(checks), 'checks': checks, 'exact_a_n_0_through_60': finite,
            'exact_b_n_1_through_60': [str(v) for v in rational], 'brute': brute,
            'root_log_jets_degrees_0_through_40': jets,
            'symbolic_transfer': {'m_series': '(-1)^m*(-m^-2+(2*log(m)+2*gamma-6)*m^-3)',
                                  'n_series': '(-1)^n*(n^-2+(8-2*gamma-2*log(n))*n^-3)',
                                  'complex_pair_n_series': '6*Re(C_omega*omega^(1-n))*n^-3'},
            'amplitudes': numerical_report, 'decimal_bounds_check': decimal_report,
            'finite_model_examples': inverses,
            'toolchain': {'python': sys.version.split()[0], 'mpmath': mp.__version__, 'sympy': sp.__version__,
                          'integer_decimal_digit_cap': sys.get_int_max_str_digits()},
            'code_sha256': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
                            for name in ('record_sum.py', 'checks.py')},
            'limitations': 'Finite arithmetic and diagnostic checks do not prove the asymptotic theorem, certify arbitrary high-order coefficients, provide effective remainder constants, establish convergence of an infinite expansion, or certify integer inverse thresholds.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', help='new JSON file outside the source package')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(certificate(), args.output)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, ValueError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
