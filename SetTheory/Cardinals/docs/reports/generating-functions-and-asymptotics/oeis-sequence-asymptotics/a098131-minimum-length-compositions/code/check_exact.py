#!/usr/bin/env python3
"""Mandatory finite exact checks; integer/Fraction arithmetic; no assertions.

Run with python -I -S -B (and also -O). Optional --output must name a new
file outside this package in an existing nonsymlinked directory.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT))
from compositions import a_count, b_count, a_gf_coefficients, b_gf_coefficients
from coefficients import coefficients, c1_formula
from independent_coefficients import independent_coefficients, derivative_polynomials
import verify_manifest as manifest


class Checks:
    def __init__(self):
        self.count = 0
        self.rejections = 0

    def check(self, condition, label):
        self.count += 1
        if not condition:
            raise RuntimeError('failed check: ' + label)

    def reject(self, operation, label):
        try:
            operation()
        except (ValueError, TypeError):
            self.rejections += 1
            return
        raise RuntimeError('missing input rejection: ' + label)


def compositions(n):
    if n == 0:
        yield ()
    else:
        for part in range(1, n + 1):
            for tail in compositions(n - part):
                yield (part,) + tail


def read_fixtures():
    document = manifest.load_json(manifest.read_regular(ROOT / 'data/oeis_fixtures.json'))
    manifest.need(type(document) is dict and set(document) == {'schema', 'snapshot_date', 'records'},
                  'fixture schema mismatch')
    manifest.need(document['schema'] == 'report189-small-oeis-fixtures-v1'
                  and document['snapshot_date'] == '2026-10-04', 'fixture identity mismatch')
    records = document['records']
    manifest.need(type(records) is list and len(records) == 3, 'fixture count mismatch')
    identities = [('A098131', 0), ('A098132', 1), ('A098133', 1)]
    for row, (identifier, offset) in zip(records, identities):
        manifest.need(type(row) is dict and set(row) == {'id', 'offset', 'terms', 'source', 'attribution'},
                      'fixture record schema mismatch')
        manifest.need(row['id'] == identifier and type(row['offset']) is int
                      and row['offset'] == offset and row['source'] == 'https://oeis.org/' + identifier,
                      'fixture identity or offset mismatch')
        manifest.need(type(row['attribution']) is str and bool(row['attribution']), 'missing attribution')
        manifest.need(type(row['terms']) is list and len(row['terms']) == 24
                      and all(type(term) is int and term >= 0 for term in row['terms']),
                      'fixture terms must be 24 nonnegative integers')
    return records


def run_checks():
    checks = Checks()
    for n in range(1, 14):
        values = list(compositions(n))
        checks.check(len(values) == 2 ** (n - 1), 'brute enumeration size ' + str(n))
        for s in range(6):
            checks.check(a_count(n, s) == sum(min(c) >= len(c) + s for c in values),
                         'brute a ' + str((n, s)))
            checks.check(b_count(n, s) == sum(min(c) == len(c) + s for c in values),
                         'brute b ' + str((n, s)))
    limit = 400
    for s in range(6):
        ga, gb = a_gf_coefficients(limit, s), b_gf_coefficients(limit, s)
        for n in range(limit + 1):
            checks.check(ga[n] == a_count(n, s), 'independent gf a ' + str((n, s)))
            checks.check(gb[n] == b_count(n, s), 'independent gf b ' + str((n, s)))
            checks.check(b_count(n, s) == a_count(n, s) - a_count(n, s + 1),
                         'difference identity ' + str((n, s)))
        for n in range(10 + 3 * s, limit):
            checks.check(a_count(n + 1, s) > a_count(n, s), 'finite a monotonicity ' + str((n, s)))
            checks.check(b_count(n + 1, s) > b_count(n, s), 'finite b monotonicity ' + str((n, s)))
    records = read_fixtures()
    for row, function in zip(records, [lambda n: a_count(n, 0), lambda n: a_count(n, 1), b_count]):
        for n, term in enumerate(row['terms'], row['offset']):
            checks.check(function(n) == term, row['id'] + ' term ' + str(n))
    grid = list(product([Q(1), Q(3, 2), Q(2), Q(5), Q(10), Q(100)],
                        [Q(0), Q(1), Q(2), Q(5), Q(1, 2)]))
    for v, s in grid:
        primary = coefficients(v, s, 3)
        secondary = independent_coefficients(v, s)
        checks.check(all(type(x) is Q for x in primary), 'Fraction output ' + str((v, s)))
        checks.check(primary[0] == 1, 'C0 ' + str((v, s)))
        checks.check(primary[1] == c1_formula(v, s), 'displayed C1 ' + str((v, s)))
        for j in range(4):
            checks.check(primary[j] == secondary[j], 'independent coefficient ' + str((v, s, j)))
        for order in range(3):
            checks.check(coefficients(v, s, order) == primary[:order + 1],
                         'truncation consistency ' + str((v, s, order)))
    polys = derivative_polynomials(4)
    checks.check(polys[2] == [Q(2), Q(6), Q(2)], 'Q2=2D')
    checks.check(polys[3] == [Q(12), Q(22), Q(6)], 'Q3=2E')
    checks.check(polys[4] == [Q(70), Q(100), Q(24)], 'Q4=2F')
    for s in range(6):
        checks.check(a_count(0, s) == 1 and b_count(0, s) == 0, 'empty convention')
        checks.check(a_count(s + 1, s) == 1 and b_count(s + 1, s) == 1, 'first nonempty term')
    for invalid in (-1, True, 1.0, '1', None, Q(1, 2)):
        for function in (a_count, b_count, a_gf_coefficients, b_gf_coefficients):
            checks.reject(lambda f=function, x=invalid: f(x), 'count n/limit ' + repr(invalid))
            checks.reject(lambda f=function, x=invalid: f(10, x), 'count s ' + repr(invalid))
    for invalid in (-1, True, 1.0, '1', None, Q(1, 2)):
        checks.reject(lambda x=invalid: coefficients(2, 0, x), 'coefficient order ' + repr(invalid))
    for invalid in (0, -1, True, 1.0, '1', None):
        checks.reject(lambda x=invalid: coefficients(x, 0, 1), 'coefficient v ' + repr(invalid))
        checks.reject(lambda x=invalid: independent_coefficients(x, 0), 'independent v ' + repr(invalid))
        checks.reject(lambda x=invalid: c1_formula(x), 'formula v ' + repr(invalid))
    for invalid in (-1, True, 1.0, '1', None):
        checks.reject(lambda x=invalid: coefficients(2, x, 1), 'coefficient s ' + repr(invalid))
        checks.reject(lambda x=invalid: independent_coefficients(2, x), 'independent s ' + repr(invalid))
        checks.reject(lambda x=invalid: c1_formula(2, x), 'formula s ' + repr(invalid))
    # Higher orders are supported; this is a consistency check, not an independent C4/C5 audit.
    high = coefficients(Q(3, 2), 1, 5)
    checks.check(high[:4] == independent_coefficients(Q(3, 2), 1), 'C5 generation preserves C0..C3')
    checks.check(len(high) == 6 and all(type(x) is Q for x in high), 'all-order generator smoke check J5')
    return {'status': 'passed', 'arithmetic': 'integer and Fraction only',
            'checks': checks.count, 'input_rejection_tests': checks.rejections,
            'total_tests': checks.count + checks.rejections,
            'brute_max_n': 13, 'independent_gf_max_n': limit, 'count_s_values': list(range(6)),
            'coefficient_grid_points': len(grid), 'independent_coefficient_order': 3,
            'independent_coefficient_comparisons': 4 * len(grid),
            'all_order_smoke_order': 5,
            'oeis_fixtures': [{'id': row['id'], 'offset': row['offset'], 'terms': len(row['terms'])}
                              for row in records],
            'floating_computations': 'not used', 'network_required': False,
            'scope': 'Finite identities and input guards; asymptotic theorems require the report proof.'}


def output_path(value):
    path = Path(value).absolute()
    manifest.need('..' not in path.parts, 'unsafe output path')
    manifest.check_directory(path.parent)
    manifest.need(not path.resolve().is_relative_to(ROOT.resolve()), 'output must be outside package')
    # xb below rejects existing files, directories and dangling links atomically.
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=output_path)
    args = parser.parse_args()
    try:
        result = run_checks()
        data = (json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')
        if args.output is not None:
            with args.output.open('xb') as stream:
                stream.write(data)
        sys.stdout.buffer.write(data)
    except (ValueError, RuntimeError, OSError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
