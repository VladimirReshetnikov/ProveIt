#!/usr/bin/env python3
"""Regenerate exact identities and NON-CERTIFIED numerical consistency checks.

Run from any working directory: python path/to/scripts/replay.py
Requires Python >=3.10 and mpmath==1.3.0; no external data or network used.
Output paths are resolved relative to this script; JSON is deterministic.
"""
from fractions import Fraction as Q
import json
from math import comb, factorial
from pathlib import Path
import sys
import mpmath as mp
sys.dont_write_bytecode = True
from exact_algebra import (gaussian_coefficients, mixed_bernoulli_coefficients,
                           recurrence_coefficients)

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / 'results'
RESULTS.mkdir(exist_ok=True)


def save(name, payload):
    (RESULTS / name).write_text(json.dumps(payload, indent=2) + '\n', encoding='utf-8')


def fmt(x, digits=70):
    return mp.nstr(x, digits, strip_zeros=False)


def mq(q):
    return mp.mpf(q.numerator) / q.denominator


def run_exact():
    d = gaussian_coefficients(12)
    recurrence_d = recurrence_coefficients(12, validate_operator=True)
    assert d == recurrence_d
    assert d[:3] == [Q(1), Q(55, 24), Q(2581, 1152)]
    c = mixed_bernoulli_coefficients(8)
    mixed = gaussian_coefficients(16, mixed=True)
    assert mixed[::2] == c
    assert all(value == 0 for value in mixed[1::2])
    assert c[:5] == [Q(1), Q(-25, 96), Q(2299, 18432),
                     Q(-1073363, 26542080), Q(-3620999, 2038431744)]
    save('exact_coefficients.json', {
        'status': 'exact rational identities in finite formal coefficient algebra',
        'asymptotic_warning': 'These identities alone prove no late-order remainder bound.',
        'd_gaussian_and_recurrence': [str(x) for x in d],
        'c_bernoulli_and_mixed_gaussian': [str(x) for x in c],
        'mixed_gaussian_t0_through_t16': [str(x) for x in mixed],
        'assertions': ['d0 through d12 agree by two algebraically independent constructions',
                       'transformed recurrence operator vanishes below degree k+4',
                       'coefficient at degree k+4 is exactly -4k, k=0,...,12',
                       'mixed Gaussian coefficients at t^(2m) equal cm for m=0,...,8',
                       'all odd mixed Gaussian coefficients through t15 vanish']})
    print('PASS exact: d0...d12; c0...c8; mixed Gaussian through t16', flush=True)
    return d, c


def run_precision(d_exact, c):
    with mp.workdps(200):
        d200 = recurrence_coefficients(100, convert=mp.mpf)
    with mp.workdps(300):
        d300 = recurrence_coefficients(100, convert=mp.mpf)
        relative = [abs(x - y) / max(mp.mpf(1), abs(y))
                    for x, y in zip(d200, d300)]
        maximum = max(relative)
        assert maximum < mp.mpf('1e-170')
        exact_errors = [abs(d300[j] - mq(d_exact[j])) / max(mp.mpf(1), abs(mq(d_exact[j])))
                        for j in range(13)]
        assert max(exact_errors) < mp.mpf('1e-280')
        constant = 2 * mp.exp(2) / mp.pi
        rows = []
        for j in [20, 40, 60, 80, 100]:
            ratio = d300[j] * 4 ** j / (constant * mp.gamma(j))
            terms = [mq(c[m]) * 4 ** (2 * m) * mp.gamma(j - 2 * m) / mp.gamma(j)
                     for m in range(5)]
            approximation = sum(terms[:4])
            residual = ratio - approximation
            scaled = residual / (4 ** 8 * mp.gamma(j - 8) / mp.gamma(j))
            rows.append({'j': j, 'normalized_ratio': fmt(ratio),
                         'first_four_terms': fmt(approximation),
                         'four_term_residual': fmt(residual),
                         'residual_divided_by_next_gamma_scale': fmt(scaled),
                         'predicted_c4': str(c[4])})
        save('high_precision.json', {
            'status': 'NON-CERTIFIED high-precision numerical consistency evidence',
            'working_decimal_precisions': [200, 300],
            'indices': '0 through 100 inclusive',
            'comparison_metric': 'abs(d200-d300)/max(1,abs(d300))',
            'max_comparison_error': fmt(maximum),
            'worst_index': relative.index(maximum),
            'asserted_comparison_threshold': '1e-170',
            'max_d300_exact_d0_through_d12_relative_error': fmt(max(exact_errors)),
            'd_at_200_digits': [fmt(x, 180) for x in d200],
            'd_at_300_digits': [fmt(x, 180) for x in d300],
            'four_term_late_model': 'sum(m=0..3) 4^(2m) cm Gamma(j-2m)/Gamma(j)',
            'late_rows': rows})
        print('PASS numerical: 200/300-digit agreement, max scaled difference =',
              fmt(maximum, 8), flush=True)
        print('j=100 four-term normalized residual =',
              rows[-1]['four_term_residual'], flush=True)
    return d300, rows


def original_integer_sequence(n):
    a = [1, 3, 16]
    for k in range(3, n + 1):
        numerator = ((3 * k * k + k - 1) * a[k - 1]
                     - (k - 1) ** 2 * (3 * k + 1) * a[k - 2]
                     + (k - 2) ** 2 * (k - 1) ** 2 * a[k - 3])
        assert numerator % k == 0
        a.append(numerator // k)
    return a[:n + 1]


def run_original_inverse():
    a = original_integer_sequence(1000)
    for n in range(31):
        direct = sum(comb(n, k) ** 2 * comb(2 * k, k) * factorial(n - k)
                     for k in range(n + 1))
        assert a[n] == direct
    assert all(a[n] >= n * a[n - 1] for n in range(2, len(a)))
    with mp.workdps(120):
        rows = []
        for n in [20, 50, 100, 200, 500, 1000]:
            y = mp.log(a[n]) + 2 + mp.log(8 * mp.pi) / 2
            base = y / mp.lambertw(y / mp.e)
            ell = mp.log(base)
            correction = (-mp.mpf(55) / (24 * ell) - 8 / ell ** 3
                          + mp.mpf(112) / (3 * ell ** 4) - 32 / ell ** 5)
            inverse = (base - 4 * mp.sqrt(base) / ell + 8 / ell ** 2
                       - 8 / ell ** 3 + correction / mp.sqrt(base))
            assert abs(base * (mp.log(base) - 1) - y) < mp.mpf('1e-110')
            rows.append({'n': n, 'N': fmt(base), 'continuous_inverse': fmt(inverse),
                         'inverse_minus_n': fmt(inverse - n),
                         'error_times_N_logN': fmt((inverse - n) * base * ell)})
    save('original_sequence_and_inverse.json', {
        'exact_status': 'Exact integers: recurrence/direct-sum match for n=0,...,30; integrality through 1000.',
        'numerical_status': 'NON-CERTIFIED continuous-asymptotic inversion checks at x=a_n.',
        'rounding_warning': 'No subunit accuracy is claimed for an unspecified integer-threshold inverse.',
        'a0_through_a30': [str(x) for x in a[:31]],
        'monotonicity_check': 'a_n >= n*a_(n-1) verified exactly for n=2,...,1000',
        'rows': rows})
    print('PASS original sequence: direct sum n<=30; integral recurrence n<=1000; inverse checks', flush=True)
    return rows


def run_late_inverse(d, c):
    with mp.workdps(180):
        constant = 2 * mp.exp(2) / mp.pi
        cst_log = mp.log(constant * mp.sqrt(2 * mp.pi))

        def log_late_model(index):
            series = sum(mq(c[m]) * 4 ** (2 * m) * mp.gamma(index - 2 * m)
                         for m in range(4))
            assert series > 0
            return mp.log(constant) - index * mp.log(4) + mp.log(series)

        rows = []
        for j in [20, 40, 60, 80, 100]:
            target = mp.log(d[j])
            z = target - cst_log
            base = z / mp.lambertw(z / (4 * mp.e))
            first = base + mp.log(base) / (2 * mp.log(base / 4))
            # Numerical root of a four-term MODEL, not an exact analytic inverse of d_j.
            root = mp.findroot(lambda u: log_late_model(u) - target,
                               (mp.mpf(j) - mp.mpf('.1'), mp.mpf(j) + mp.mpf('.1')))
            assert abs(log_late_model(root) - target) < mp.mpf('1e-160')
            rows.append({'j': j, 'J': fmt(base), 'Lambert_first_correction': fmt(first),
                         'first_corrected_minus_j': fmt(first - j),
                         'four_term_model_root': fmt(root),
                         'model_root_minus_j': fmt(root - j)})
    save('late_inverse_models.json', {
        'status': 'NON-CERTIFIED numerical checks of continuous asymptotic models only',
        'first_model': 'J=Z/W(Z/(4e)); J+log(J)/(2log(J/4)); Z=log(x)-log(2e^2 sqrt(2pi)/pi)',
        'refined_model': 'Numerical inversion of (2e^2/pi)4^(-u) sum(m=0..3)4^(2m)cm Gamma(u-2m)',
        'warning': 'No all-j monotonicity claim, no exact interpolation of d_j, and no integer inverse error theorem.',
        'rows': rows})
    print('PASS late inverse: Lambert and four-term continuous-model residual checks', flush=True)
    return rows


def write_tables(late_rows, original_rows, inverse_rows):
    def short(value, digits=14):
        with mp.workdps(80):
            number = mp.nstr(mp.mpf(value), digits)
        if 'e' in number:
            mantissa, exponent = number.split('e')
            return '$' + mantissa + r'\times 10^{' + str(int(exponent)) + '}$'
        return '$' + number + '$'
    lines = [r'% Generated deterministically by scripts/replay.py.',
             r'% High-precision, non-certified numerical evidence.',
             r'\begin{tabular}{r r r}',
             r'$j$ & $d_j4^j/(C\Gamma(j))$ & four-term residual \\', r'\hline']
    for row in late_rows:
        lines.append(f"{row['j']} & {short(row['normalized_ratio'], 17)} & "
                     f"{short(row['four_term_residual'], 8)} " + r'\\')
    lines += [r'\end{tabular}', '', r'\begin{tabular}{r r r}',
              r'$n$ & continuous inverse error & error $\cdot N\log N$ \\', r'\hline']
    for row in original_rows:
        lines.append(f"{row['n']} & {short(row['inverse_minus_n'])} & "
                     f"{short(row['error_times_N_logN'])} " + r'\\')
    lines += [r'\end{tabular}', '', r'\begin{tabular}{r r r}',
              r'$j$ & first-corrected inverse error & four-term model inverse error \\', r'\hline']
    for row in inverse_rows:
        lines.append(f"{row['j']} & {short(row['first_corrected_minus_j'])} & "
                     f"{short(row['model_root_minus_j'], 8)} " + r'\\')
    lines += [r'\end{tabular}', '']
    (RESULTS / 'numerical_tables.tex').write_text('\n'.join(lines), encoding='utf-8')


def main():
    d_exact, c = run_exact()
    d, late_rows = run_precision(d_exact, c)
    original_rows = run_original_inverse()
    inverse_rows = run_late_inverse(d, c)
    write_tables(late_rows, original_rows, inverse_rows)
    print('All checks passed; outputs in', RESULTS.name, flush=True)


if __name__ == '__main__':
    main()
