#!/usr/bin/env python3
"""Offline finite exact checks for Report192, active under Python -O.

Forty-nine recurrence coefficients n=0..48; all height cells through n=48;
independent rooted Pruefer trees through n=7; level profiles through n=12.
No finite computation certifies the analytic asymptotic conclusions.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from math import factorial
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'code'))
import verify_manifest as manifest
import tower
import prufer
import profiles

FIXTURE_SHA256 = '269fcf340a5828d6c0ebdfdbce420f74286aff8deb1598d4052e77e358589810'
GENERATED_SHA256 = '33f87d0e380c0d11336cc341e5d04cc0485692cba302beac3023a53b8b924444'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')


def validate_fixture(data):
    need(type(data) is dict and set(data) == {'schema', 'reviewed_utc_date', 'A096537', 'A096542'}, 'fixture schema')
    need(data['schema'] == 'report192-bounded-oeis-fixtures-v1' and data['reviewed_utc_date'] == '2026-10-04', 'fixture identity/date')
    row = data['A096537']
    need(type(row) is dict and set(row) == {'source', 'credit', 'offset', 'terms', 'official_terms_used', 'official_bfile_link', 'official_bfile_advertised_range', 'official_bfile_used'}, 'sequence fixture schema')
    need(row['source'] == 'https://oeis.org/A096537' and row['credit'] == 'Paul D. Hanna (2004); b-file credited to Vaclav Kotesovec', 'sequence source/credit')
    need(type(row['offset']) is int and row['offset'] == 0, 'sequence offset')
    need(type(row['official_terms_used']) is int and row['official_terms_used'] == 15, 'official prefix size')
    need(type(row['terms']) is list and len(row['terms']) == 15 and all(type(v) is int and v > 0 for v in row['terms']), 'sequence term domain')
    need(row['official_bfile_link'] == 'https://oeis.org/A096537/b096537.txt', 'b-file citation')
    need(type(row['official_bfile_advertised_range']) is list and all(type(v) is int for v in row['official_bfile_advertised_range']) and row['official_bfile_advertised_range'] == [0, 200], 'b-file advertised range')
    need(row['official_bfile_used'] is False, 'unverified official b-file must not be claimed')
    triangle = data['A096542']
    need(type(triangle) is dict and set(triangle) == {'source', 'credit', 'row_offset', 'rows', 'official_rows_used'}, 'triangle fixture schema')
    need(triangle['source'] == 'https://oeis.org/A096542' and triangle['credit'] == 'Paul D. Hanna (2004)', 'triangle source/credit')
    need(type(triangle['row_offset']) is int and triangle['row_offset'] == 0 and type(triangle['official_rows_used']) is int and triangle['official_rows_used'] == 9, 'triangle row count/offset')
    need(type(triangle['rows']) is list and len(triangle['rows']) == 9, 'triangle rows')
    for n, values in enumerate(triangle['rows']):
        need(type(values) is list and len(values) == n+1 and all(type(v) is int and v >= 0 for v in values), 'triangle row domain')
    return data


def parse_fixture(raw):
    need(type(raw) is bytes, 'fixture must be bytes')
    need(hashlib.sha256(raw).hexdigest() == FIXTURE_SHA256, 'official prefix checksum mismatch')
    return validate_fixture(manifest.load_json(raw.decode('utf-8')))


def validate_generated(data):
    need(type(data) is dict and set(data) == {'schema', 'origin', 'source_definition', 'offset', 'maximum_n', 'coefficients'}, 'generated regression schema')
    need(data['schema'] == 'report192-generated-coefficients-v1' and data['origin'] == 'Author-generated exact recurrence; not an official OEIS b-file' and data['source_definition'] == 'https://oeis.org/A096537', 'generated regression provenance')
    need(type(data['offset']) is int and data['offset'] == 0 and type(data['maximum_n']) is int and data['maximum_n'] == 48, 'generated regression range')
    need(type(data['coefficients']) is list and len(data['coefficients']) == 49 and all(type(v) is int and v > 0 for v in data['coefficients']), 'generated coefficient domain')
    return data


def parse_generated(raw):
    need(type(raw) is bytes, 'generated input must be bytes')
    need(hashlib.sha256(raw).hexdigest() == GENERATED_SHA256, 'generated regression checksum mismatch')
    return validate_generated(manifest.load_json(raw.decode('utf-8')))


def rejected(call):
    try:
        call()
    except (ValueError, TypeError, ZeroDivisionError):
        return
    raise ValueError('invalid input unexpectedly accepted')


def input_guards(fixture, raw, generated, generated_raw):
    cases = []
    for invalid in (True, False, -1, 201, 1.0, '1', None, Fraction(1)):
        cases += [lambda v=invalid: tower.coefficients(v),
                  lambda v=invalid: tower.finite_tower(1, v),
                  lambda v=invalid: tower.finite_tower(v, 1)]
    for invalid in (True, False, 0, -1, 1.0, '1', None, Fraction(-1, 2)):
        cases += [lambda v=invalid: tower.finite_tower(2, 2, v)]
    for invalid in (True, False, -1, 8, 1.0, '1', None, Fraction(1)):
        cases += [lambda v=invalid: prufer.enumerate_trees(v)]
    for invalid in (True, False, -1, 15, 1.0, '1', None, Fraction(1)):
        cases += [lambda v=invalid: profiles.height_weights(v),
                  lambda v=invalid: list(profiles.compositions(v))]
    for sequence, vertices in (([], True), ([], 0), ([], 1), ([], 9), ([0], 2), ([], 3), ([True], 3), ([-1], 3), ([3], 3), ('0', 3), ([0.0], 3)):
        cases.append(lambda s=sequence, v=vertices: prufer.decode(s, v))
    cases += [lambda: prufer.depths([[], []]), lambda: prufer.depths([[2], []]),
              lambda: parse_fixture(raw+b' '), lambda: parse_fixture(raw.decode('utf-8')),
              lambda: parse_generated(generated_raw+b' '), lambda: parse_generated(generated_raw.decode('utf-8')),
              lambda: manifest.load_json('{"x":1,"x":2}'), lambda: manifest.load_json('{"x":NaN}')]
    changes = [lambda d: d['A096537']['terms'].__setitem__(0, True),
               lambda d: d['A096537']['terms'].pop(),
               lambda d: d['A096537'].__setitem__('offset', False),
               lambda d: d['A096537'].__setitem__('official_terms_used', 201),
               lambda d: d['A096537'].__setitem__('official_bfile_used', True),
               lambda d: d['A096537'].__setitem__('source', 'https://example.org'),
               lambda d: d['A096537'].__setitem__('official_bfile_advertised_range', [False, 200]),
               lambda d: d['A096542']['rows'][1].__setitem__(0, False),
               lambda d: d['A096542']['rows'].pop(),
               lambda d: d.__setitem__('unrecognized', 1),
               lambda d: d.__setitem__('schema', 'wrong')]
    for change in changes:
        altered = copy.deepcopy(fixture)
        change(altered)
        cases.append(lambda d=altered: validate_fixture(d))
    for change in [lambda d: d['coefficients'].__setitem__(10, True),
                   lambda d: d['coefficients'].pop(),
                   lambda d: d.__setitem__('maximum_n', True),
                   lambda d: d.__setitem__('origin', 'official OEIS data')]:
        altered = copy.deepcopy(generated)
        change(altered)
        cases.append(lambda d=altered: validate_generated(d))
    for original, field, parser in [(fixture['A096537'], 'terms', parse_fixture),
                                     (generated, 'coefficients', parse_generated)]:
        altered = copy.deepcopy(fixture if field == 'terms' else generated)
        values = altered['A096537']['terms'] if field == 'terms' else altered['coefficients']
        values[-1] += 1
        cases.append(lambda d=altered, p=parser: p(canonical(d)))
    for case in cases:
        rejected(case)
    return len(cases)


def profile_checks(max_n=12):
    need(type(max_n) is int and 0 <= max_n <= 12, 'profile-check bound')
    previous = [1] + [0] * max_n
    table = [[0] * (max_n+1) for _ in range(max_n+1)]
    table[0][0] = 1
    for height in range(1, max_n+1):
        current = tower.finite_tower(height, max_n)
        for n in range(max_n+1):
            table[n][height] = current[n] - previous[n]
        previous = current
    cells = 0
    for n in range(max_n+1):
        values = profiles.height_weights(n)
        need(values == table[n][:n+1], 'independent level-profile/tower mismatch at n=' + str(n))
        cells += len(values)
    return {'max_n': max_n, 'height_cells_including_zero': cells,
            'method': 'exact positive level-composition sum'}


def run_checks():
    raw = manifest.read_regular(ROOT / 'data/oeis_fixtures.json', 16384)
    generated_raw = manifest.read_regular(ROOT / 'data/generated_coefficients_48.json', 32768)
    fixture, generated = parse_fixture(raw), parse_generated(generated_raw)
    guards = input_guards(fixture, raw, generated, generated_raw)
    nmax = 48
    weights = tower.height_weights(nmax)
    coefficients = tower.coefficients(nmax)
    need(coefficients == generated['coefficients'], 'generated coefficient regression mismatch')
    need(coefficients[:15] == fixture['A096537']['terms'], 'official 15-term prefix mismatch')
    positivity_cells = 0
    for n in range(nmax+1):
        need(sum(weights[n]) == coefficients[n], 'height decomposition n=' + str(n))
        for h in range(nmax+1):
            need(type(weights[n][h]) is int and weights[n][h] >= 0, 'height positivity')
            need(h <= n or weights[n][h] == 0, 'height least degree')
            positivity_cells += 1
        need(weights[n][n] == factorial(n)**2, 'path diagonal')
    monotonicity = 0
    for mark in (1, 2, 4):
        marked = [sum(v * mark**h for h, v in enumerate(row)) for row in weights]
        for n in range(1, nmax+1):
            need(marked[n] >= mark * n*n * marked[n-1], 'marked monotonicity')
            monotonicity += 1
    trees = []
    shifted = tower.finite_tower(7, 7, 2)
    height_cells = 0
    for n in range(8):
        row = prufer.enumerate_trees(n)
        need(row['depth_product_sum'] == coefficients[n], 'independent tree coefficient mismatch')
        need(row['height_sums'] == weights[n][:n+1], 'independent tree height mismatch')
        need(row['shift_two_sum'] == shifted[n], 'independent shifted tree mismatch')
        height_cells += n+1
        trees.append(row)
    triangle_cells = 0
    for y in (Fraction(1, 2), 1, 2, 3):
        values = tower.finite_tower(8, 8, y)
        for n, row in enumerate(fixture['A096542']['rows']):
            need(sum(c * y**k for k, c in enumerate(row)) == values[n], 'official polynomial triangle mismatch')
            triangle_cells += 1
    for n, row in enumerate(fixture['A096542']['rows'][1:], 1):
        need(row[1] == n * coefficients[n-1], 'corrected triangle first-column identity')
        need(row[n] == (n+1)**(n-1), 'triangle Cayley diagonal')
    return {'status': 'passed', 'report': 192, 'arithmetic': 'integer and Fraction only',
            'required_third_party_dependencies': [], 'fixture_sha256': FIXTURE_SHA256,
            'generated_regression_sha256': GENERATED_SHA256,
            'official_A096537_terms_checked': 15, 'official_A096537_indices': [0, 14],
            'official_A096537_bfile_used': False,
            'official_A096542_complete_rows_checked': 9,
            'official_polynomial_evaluations': triangle_cells,
            'exact_coefficients_max_n': nmax, 'exact_coefficients': coefficients,
            'height_table_nonnegative_cells_checked': positivity_cells,
            'height_weights_n0_to_n7': [row[:n+1] for n, row in enumerate(weights[:8])],
            'path_diagonal_checks': nmax+1, 'marked_monotonicity_checks': monotonicity,
            'independent_prufer': {'max_n': 7, 'root': 0, 'rows': trees,
                'trees_n1_to_n7': sum(row['trees'] for row in trees[1:]),
                'height_cells_including_zero': height_cells, 'positive_height_cells': 28,
                'shift_two_coefficient_checks': 8},
            'independent_profiles': profile_checks(),
            'input_and_fixture_rejection_tests': guards,
            'checks_enabled_under_python_optimization': True,
            'scope': 'Finite exact checks supplement the proofs in Report192. The generated '
                     'n=15..48 data are not official b-file terms. No finite replay certifies '
                     'asymptotic convergence, an Airy limit, a remainder bound, an effective onset, '
                     'or any numerical amplitude digits.'}


def checked_output(path):
    output = Path(path).absolute()
    need('..' not in output.parts, 'unsafe output path')
    manifest.check_directory(output.parent)
    need(not output.resolve().is_relative_to(ROOT.resolve()), 'output must be outside source tree')
    need(not os.path.lexists(output), 'refusing existing output')
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='new file outside the source tree')
    args = parser.parse_args()
    try:
        output = checked_output(args.output) if args.output is not None else None
        payload = canonical(run_checks())
        if output is not None:
            with output.open('xb') as stream:
                stream.write(payload)
        sys.stdout.buffer.write(payload)
    except (ValueError, TypeError, OSError, ZeroDivisionError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
