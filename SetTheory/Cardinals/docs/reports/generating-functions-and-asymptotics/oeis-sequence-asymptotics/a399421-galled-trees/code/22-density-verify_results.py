#!/usr/bin/env python3
"""Verify regenerated results without interpreting rounded decimals as certificates."""
import argparse
from decimal import Decimal, localcontext
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
D = Decimal


def read_json(path):
    return json.loads(path.read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def compare_numeric(actual, expected, tolerance, label):
    """Recursively compare structures; integer identifiers remain exact."""
    if isinstance(expected, dict):
        require(isinstance(actual, dict) and actual.keys() == expected.keys(), label + ': keys differ')
        for key in expected:
            compare_numeric(actual[key], expected[key], tolerance, f'{label}.{key}')
    elif isinstance(expected, list):
        require(isinstance(actual, list) and len(actual) == len(expected), label + ': length differs')
        for index, value in enumerate(expected):
            compare_numeric(actual[index], value, tolerance, f'{label}[{index}]')
    elif isinstance(expected, int):
        require(type(actual) is int and actual == expected, label + ': integer differs')
    else:
        a, b = D(str(actual)), D(str(expected))
        require(a.is_finite() and b.is_finite(), label + ': nonfinite value')
        error = abs(a-b)
        bound = D(tolerance)*max(D(1), abs(a), abs(b))
        require(error <= bound, f'{label}: |difference|={error} > {bound}')


def compare_log(actual_path, expected_path):
    """Compare each printed number to four units in its last displayed place."""
    pattern = re.compile(r'(?<![A-Za-z0-9_])[-+]?(?:\d+\.\d*|\.\d+|\d+)(?:[eE][-+]?\d+)?')
    actual, expected = actual_path.read_text(), expected_path.read_text()
    require(pattern.sub('#', actual).split() == pattern.sub('#', expected).split(),
            expected_path.name + ': log structure differs')
    aa, bb = pattern.findall(actual), pattern.findall(expected)
    require(len(aa) == len(bb), expected_path.name + ': printed numeric count differs')
    for index, (a, b) in enumerate(zip(aa, bb)):
        x, y = D(a), D(b)
        tol = D(0) if re.fullmatch(r'[-+]?\d+', b) else max(D('1e-65'), 4*D(1).scaleb(y.as_tuple().exponent))
        require(x.is_finite() and abs(x-y) <= tol,
                f'{expected_path.name} token {index}: {a} differs from {b}')
    return len(bb)


def stability_summary(base, comparison, label, bound):
    differences = {}
    for key in ('rho', 'tau', 'B', 'Phi_z', 'Phi_yy', 'gamma', 'mu', 'variance', 'eta', 'C'):
        differences[key] = str(abs(D(base[key])-D(comparison[key])))
    for key in ('puiseux', 'corrections'):
        for index, value in enumerate(base[key]):
            differences[f'{key}[{index}]'] = str(abs(D(value)-D(comparison[key][index])))
    require(all(D(value) < D(bound) for value in differences.values()),
            f'{label}: empirical stability threshold {bound} exceeded')
    return {'comparison': label, 'absolute_threshold': bound,
            'maximum_absolute_difference': str(max(map(D, differences.values()))),
            'absolute_differences': differences}


def verify(output, quick=False, amplitude=True):
    expected = ROOT / 'results' / 'expected'
    public = read_json(ROOT / 'data' / 'oeis-reference.json')
    regenerated = read_json(output / 'independent-rows.json')
    baseline_rows = read_json(expected / 'independent-rows.json')
    n_max = 27 if quick else 160
    rows = regenerated['rows']
    require(len(rows) == n_max+1, 'wrong row cutoff')
    require(rows == baseline_rows['rows'][:n_max+1], 'exact coefficient rows differ')
    require(regenerated['totals'] == baseline_rows['totals'][:n_max+1], 'exact row sums differ')
    require(rows[0] == [0], 'row zero must be zero')
    for n, row in enumerate(rows[1:], 1):
        require(len(row) == (n-1)//2+1 and all(type(x) is int and x > 0 for x in row),
                f'row {n}: support, positivity, or integrality differs')
        require(sum(row) == regenerated['totals'][n], f'row {n}: sum differs')
    expected_stats = [s for s in baseline_rows['statistics'] if s['n'] <= n_max]
    compare_numeric(regenerated['statistics'], expected_stats, '1e-12', 'finite-size statistics')
    scalar = public['A397952']
    start = scalar['offset']
    require(regenerated['totals'][start:start+len(scalar['values'])] == scalar['values'],
            'A397952 public initial terms differ')
    triangle = public['A399421']
    cells = 0
    for item in triangle['rows']:
        require(rows[item['n']] == item['values'], f"A399421 row {item['n']} differs")
        cells += len(item['values'])
    require(cells == triangle['cells'] == 49, 'triangle cell count differs')
    report = {'status': 'passed', 'mode': 'quick' if quick else 'full',
              'exact_generated_max_n': n_max,
              'exact_generated_cells_including_zero': sum(map(len, rows)),
              'oeis_reference': {'A397952_terms': len(scalar['values']),
                                 'A399421_rows': len(triangle['rows']), 'A399421_cells': cells},
              'numerical_checks': [],
              'qualification': 'Numerical tolerance and cutoff/precision comparisons are not interval certificates.'}
    if not quick:
        # Stored constants have 75 significant digits; the 60-digit run has fewer reliable digits.
        for filename, tolerance in [('constants.json', '1e-65'),
                                    ('stability/cutoff120-dps80.json', '1e-65'),
                                    ('stability/cutoff160-dps60.json', '1e-52')]:
            compare_numeric(read_json(output/filename), read_json(expected/filename), tolerance, filename)
            report['numerical_checks'].append({'file': filename, 'scaled_absolute_tolerance': tolerance})
        density, reference_density = read_json(output/'density-checks.json'), read_json(expected/'density-checks.json')
        require(len(density) == len(reference_density) == 3, 'density count differs')
        for index, (a, b) in enumerate(zip(density, reference_density)):
            require(a.keys() == b.keys(), f'density[{index}]: keys differ')
            for key in ('alpha', 'u', 'rho', 'beta', 'e1'):
                compare_numeric(a[key], b[key], '1e-40', f'density[{index}].{key}')
            compare_numeric(a['checks'], b['checks'], '1e-27', f'density[{index}].checks')
        report['numerical_checks'].append({'file': 'density-checks.json',
                                          'parameter_tolerance': '1e-40', 'relative_error_tolerance': '1e-27'})
        base = read_json(output/'constants.json')
        summary = {'qualification': report['qualification'], 'reference': {'row_cutoff': 160, 'working_dps': 80},
                   'comparisons': [stability_summary(base, read_json(output/'stability/cutoff120-dps80.json'),
                                                     'cutoff120-dps80 versus cutoff160-dps80', '1e-62'),
                                   stability_summary(base, read_json(output/'stability/cutoff160-dps60.json'),
                                                     'cutoff160-dps60 versus cutoff160-dps80', '1e-50')]}
        (output/'stability-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
        report['printed_numeric_tokens_checked'] = {
            'numerics.txt': compare_log(output/'numerics.txt', expected/'numerics.txt'),
            'density-numerics.txt': compare_log(output/'density-numerics.txt', expected/'density-numerics.txt')}
    if amplitude:
        a = read_json(output/'amplitude-check.json')
        compare_numeric(a, read_json(expected/'amplitude-check.json'), '1e-65', 'amplitude diagnostic')
        if not quick:
            base = read_json(output/'constants.json')
            for scalar_key, base_key in [('r', 'rho'), ('s', 'tau'), ('delta', 'gamma'),
                                         ('phit', 'Phi_z'), ('phiww', 'Phi_yy')]:
                compare_numeric(a[scalar_key], base[base_key], '1e-65', 'independent scalar versus bivariate '+base_key)
        report['numerical_checks'].append({'file': 'amplitude-check.json', 'scaled_absolute_tolerance': '1e-65'})
    report['amplitude_diagnostic'] = 'passed' if amplitude else 'skipped by request'
    (output/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'results/regenerated')
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--skip-amplitude', action='store_true')
    args = parser.parse_args()
    with localcontext() as context:
        context.prec = 110
        report = verify(args.output_dir, args.quick, not args.skip_amplitude)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
