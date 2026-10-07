#!/usr/bin/env python3
"""Offline integer/Fraction checks for Report191; no numerical certification.

Default scope is geometry through 250000, global brute force through 4096,
64 supplied OEIS terms, and independent inverse-series checks through order12.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'code'))
import verify_manifest as manifest
import spiral
import check_geometry as geometry
import inverse_series as series
import independent_series as independent

FIXTURE_SHA256 = 'eb762de550b910ef3d35983e70341dc04d885e562591e01043679377831b4c5a'
DELTA_SIX = [F(0), F(1), F(-5, 2), F(10, 3), F(-29, 12), F(-14, 5), F(403, 30)]
INVERSE_SIX = [F(1), F(2), F(-1), F(-3), F(10, 3), F(-1, 6), F(-389, 60)]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')


def validate_fixture(data):
    need(type(data) is dict and set(data) == {'schema', 'reviewed_utc_date', 'integer_sequences'}, 'fixture schema')
    need(data['schema'] == 'report191-bounded-oeis-fixtures-v1'
         and data['reviewed_utc_date'] == '2026-10-04', 'fixture identity/date')
    rows = data['integer_sequences']
    need(type(rows) is dict and set(rows) == {'A078510'}, 'sequence fixture set')
    row = rows['A078510']
    need(type(row) is dict and set(row) == {'offset', 'terms', 'source',
         'source_record_revision', 'source_record_date', 'credit'}, 'term row schema')
    need(type(row['offset']) is int and row['offset'] == 0, 'term offset')
    need(type(row['terms']) is list and len(row['terms']) == 64, 'term count')
    need(all(type(v) is int and v >= 0 for v in row['terms']), 'term integer domain')
    need(row['source'] == 'https://oeis.org/A078510', 'term source')
    need(type(row['source_record_revision']) is int and row['source_record_revision'] == 21
         and row['source_record_date'] == '2025-09-11', 'source record revision')
    need(row['credit'] == 'Neil Fernandez; recurrence credited to Antti Karttunen', 'source credit')
    return data


def parse_fixture(raw):
    need(type(raw) is bytes, 'fixture input must be bytes')
    need(hashlib.sha256(raw).hexdigest() == FIXTURE_SHA256, 'bounded fixture checksum mismatch')
    return validate_fixture(manifest.load_json(raw.decode('utf-8')))


def rejected(call):
    try:
        call()
    except (TypeError, ValueError, ZeroDivisionError):
        return
    raise ValueError('invalid input unexpectedly accepted')


def input_guards(fixture, raw):
    cases = []
    for invalid in (True, False, 1.0, '1', None, F(1), -1, spiral.MAX_INDEX + 1):
        cases += [lambda v=invalid: spiral.predecessor(v),
                  lambda v=invalid: spiral.predecessors(v),
                  lambda v=invalid: spiral.values(v),
                  lambda v=invalid: list(geometry.spiral_points(v))]
    for invalid in (0, -1, 41, True, 1.0, '12', None, F(12)):
        cases += [lambda v=invalid: series.derive(v), lambda v=invalid: independent.derive(v)]
    for invalid in (True, 1.0, None, -1, 2000003):
        cases += [lambda v=invalid: spiral.quarter(v)]
    for invalid in (0, 1, True, 1.0, None, -1, 2000003):
        cases += [lambda v=invalid: geometry.corner_point(v)]
    for invalid in (None, (), [], [True], [-1], [0, 0, 1], [0, 0, 0, -1], [0, 0, 0, 1]):
        cases.append(lambda v=invalid: spiral.validate_predecessors(v))
    for invalid in (None, [], [0], [F(0)] * 12, [True] * 13, [0.0] * 13):
        cases += [lambda v=invalid: series.exponential(v, 12),
                  lambda v=invalid: series.logarithm(v, 12)]
    cases += [lambda: series.exponential([1] + [0]*12, 12),
              lambda: series.logarithm([0]*13, 12),
              lambda: independent.exp_by_powers({0: F(1)}, 12),
              lambda: geometry.nearest_earlier_nonpredecessor((0, 0), {}, 2),
              lambda: geometry.run_checks([], 63, 8),
              lambda: geometry.run_checks([0]*64, 62, 8),
              lambda: geometry.run_checks([0]*64, 63, 64),
              lambda: parse_fixture(raw+b' '), lambda: parse_fixture(raw.decode('utf-8')),
              lambda: manifest.load_json('{"x":1,"x":2}'),
              lambda: manifest.load_json('{"x":NaN}')]
    mutations = [lambda d: d['integer_sequences']['A078510']['terms'].__setitem__(0, True),
                 lambda d: d['integer_sequences']['A078510'].__setitem__('offset', False),
                 lambda d: d['integer_sequences']['A078510']['terms'].pop(),
                 lambda d: d['integer_sequences']['A078510'].__setitem__('source', 'https://example.org/'),
                 lambda d: d['integer_sequences']['A078510'].__setitem__('source_record_revision', True),
                 lambda d: d.__setitem__('unrecognized', 1),
                 lambda d: d.__setitem__('schema', 'wrong')]
    for change in mutations:
        altered = copy.deepcopy(fixture)
        change(altered)
        cases.append(lambda d=altered: validate_fixture(d))
    altered = copy.deepcopy(fixture)
    altered['integer_sequences']['A078510']['terms'][15] += 1
    cases.append(lambda: parse_fixture(canonical(altered)))
    for case in cases:
        rejected(case)
    return len(cases)


def series_checks():
    delta, factor = series.derive(12)
    other_delta, other_factor = independent.derive(12)
    need((delta, factor) == (other_delta, other_factor), 'independent inverse-series coefficients')
    need(delta[:7] == DELTA_SIX and factor[:7] == INVERSE_SIX, 'six displayed coefficients')
    for n in range(1, 13):
        expected = (delta[:n+1], factor[:n+1])
        need(series.derive(n) == expected, 'generator truncation consistency')
        need(independent.derive(n) == expected, 'independent truncation consistency')
    return {'order': 12, 'tested_orders': list(range(1, 13)),
            'delta_coefficients': list(map(str, delta)),
            'inverse_factor_coefficients': list(map(str, factor)),
            'displayed_nonconstant_coefficients_checked_per_series': 6,
            'independent_methods': ['triangular logarithm recurrence',
                                   'sparse factorial exponential and rational division'],
            'identities': ['delta + log(Q) = 0', 'exp(delta) Q = 1', 'R Q^2 = (1+u delta)^2'],
            'scope': 'Exact finite formal identities only; analytic germ existence is proved in Report191'}


def cancellation_checks():
    # Finite exact checks of the displayed rational transport cancellation.
    count = 0
    for w in (F(1, 10), F(1), F(2), F(7), F(100)):
        for theta in (F(0), F(1, 7), F(1, 2), F(6, 7), F(1)):
            s_times_r2 = w*w/(4*(1+w)) * (F(1, 8) + 1/(1+w))
            delta = -3-2*theta
            residual = ((1+w)*s_times_r2 + w*w/F(16)*(2*theta-1)
                        + (delta-F(1, 2))*w*w/F(16) + w**3/(4*(1+w)))
            need(residual == 0, 'rational transport cancellation')
            count += 1
    return count


def run_checks():
    raw = manifest.read_regular(ROOT / 'data/oeis_fixtures.json', 16384)
    fixture = parse_fixture(raw)
    guards = input_guards(fixture, raw)
    coefficients = series_checks()
    listed = fixture['integer_sequences']['A078510']['terms']
    need(spiral.values(63) == listed, 'formula-generated OEIS terms')
    geometric = geometry.run_checks(listed, 250000, 4096)
    rows = spiral.predecessors(4096)
    need(spiral.validate_predecessors(rows) == rows, 'valid predecessor domain')
    corner_checks = 0
    for k in range(6, 1002):
        q = spiral.quarter(k)
        need(q-spiral.quarter(k-4) == 2*k-4, 'quarter-square delay identity')
        need(spiral.predecessor(q-1) == spiral.predecessor(q) == spiral.predecessor(q+1),
             'corner triple-use identity')
        corner_checks += 1
    return {'status': 'passed', 'report': 191, 'arithmetic': 'integer and Fraction only',
            'required_third_party_dependencies': [], 'fixture_sha256': FIXTURE_SHA256,
            'geometry': geometric, 'inverse_germ': coefficients,
            'input_and_fixture_rejection_tests': guards,
            'corner_identity_checks': corner_checks,
            'exact_transport_cancellation_samples': cancellation_checks(),
            'checks_enabled_under_python_optimization': True,
            'scope': 'Finite exact checks supplement the proofs in Report191. '
                     'No finite replay proves asymptotic convergence, a remainder bound, '
                     'an effective onset, or any numerical amplitude digits.'}


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
