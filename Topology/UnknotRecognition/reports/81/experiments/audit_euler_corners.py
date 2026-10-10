#!/usr/bin/env python3
"""Check the Euler-corner reduction against complete frozen standard rays.

The declared stratum is exactly the independently replayed cases in the
main audit: all raw-nullity-three sectors and three lower-nullity sectors
per source. This is an exact mathematical comparison, not a timing of the
proposed optimized precheck. Obtaining domain corners here deliberately
uses the existing complete planar plan; canonical lifts use the baseline
kernel method and native Euler evaluation. Neither timed producer changes.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, lcm
from pathlib import Path
import platform
import sys
import time

from fixtures import occupied, vector_key, ray_digest

ROOT = Path(__file__).resolve().parents[1]


def primitive(values):
    denominator = lcm(*(x.denominator for x in values))
    integers = [int(x * denominator) for x in values]
    divisor = gcd(*integers)
    if not divisor or any(x < 0 for x in integers):
        raise AssertionError('invalid normalized corner direction')
    return tuple(x // divisor for x in integers)


def ratio(value):
    return None if value is None else [value.numerator, value.denominator]


def run(args):
    fast = args.fast.resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.normal_sector import build_sector_kernel, _source_hash
    from fastunknot.sector_planar import sector_planar_plan
    from fastunknot.normal_surface_geometry import _coordinates

    raw_corpus = args.corpus.read_bytes()
    raw_audit = args.audit.read_bytes()
    corpus = json.loads(raw_corpus)
    audit = json.loads(raw_audit)
    assert sha256(raw_corpus).hexdigest() == audit['corpus_sha256']
    sources = {record['id']: record for record in corpus['records']}
    counts = Counter()
    cases = []
    started = time.perf_counter()
    for recorded_source in audit['records']:
        source = sources[recorded_source['id']]
        triangulation = source['triangulation']
        standards = [(set(occupied(s['coordinates'])), s['coordinates'])
                     for s in source['standard_vertices']]
        for case in recorded_source['cases']:
            if not case['independently_replayed']:
                continue
            support = tuple(tuple(pair) for pair in case['allowed_types'])
            selected = set(support)
            expected = [rows for used, rows in standards
                        if used and used <= selected]
            expected_keys = {vector_key(rows) for rows in expected}
            assert len(expected_keys) == len(expected) == case['ray_count']
            assert ray_digest(expected) == case['ray_sha256']
            kernel = build_sector_kernel(triangulation, support)
            assert len(kernel.basis) == case['matching_nullity'] <= 3
            plan = sector_planar_plan(kernel)
            assert len(plan['points']) == len(expected)
            corner_records = []
            corner_values = []
            corner_keys = set()
            for point in plan['domain']:
                values = list(plan['q_origin'])
                for coordinate, direction in zip(point, plan['q_directions']):
                    for j, value in enumerate(direction):
                        values[j] += coordinate * value
                assert sum(values) == 1 and all(v >= 0 for v in values)
                q = primitive(values)
                rows = kernel.lift(q)
                key = vector_key(rows)
                assert key in expected_keys, ('corner is not standard-extreme',
                                               source['id'], support, q)
                corner_keys.add(key)
                chi = _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic']
                normalized = Fraction(chi, sum(q))
                corner_values.append(normalized)
                corner_records.append(dict(quadrilaterals=q,
                    euler_characteristic=chi, normalized_euler=ratio(normalized)))
            assert len(corner_keys) == len(corner_records)
            full_values = []
            for rows in expected:
                chi = _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic']
                weight = sum(rows[t][4 + typ] for t, typ in support)
                assert weight > 0
                full_values.append(Fraction(chi, weight))
            corner_maximum = max(corner_values, default=None)
            full_maximum = max(full_values, default=None)
            assert corner_maximum == full_maximum, (
                'normalized Euler maximum mismatch', source['id'], support,
                corner_maximum, full_maximum)
            assert any(x > 0 for x in corner_values) == any(x > 0 for x in full_values)
            label = ('empty' if corner_maximum is None else
                     'positive' if corner_maximum > 0 else 'nonpositive')
            counts['cases'] += 1
            counts['nullity_' + str(len(kernel.basis))] += 1
            counts['section_dimension_' + str(plan['section_dimension'])] += 1
            counts[label] += 1
            counts['corner_evaluations'] += len(corner_values)
            counts['complete_ray_occurrences'] += len(full_values)
            counts['additional_ray_evaluations_avoided'] += len(full_values) - len(corner_values)
            counts['strict_reductions'] += int(len(corner_values) < len(full_values))
            cases.append(dict(id=source['id'], allowed_types=support,
                source_sha256=_source_hash(triangulation),
                matching_nullity=len(kernel.basis),
                section_dimension=plan['section_dimension'], status=label,
                corner_count=len(corner_values), complete_ray_count=len(full_values),
                normalized_maximum=ratio(corner_maximum), corners=corner_records))
    result = dict(schema='planar-euler-corner-audit-v1', status='PASS',
        baseline_commit=audit['baseline_commit'], python=platform.python_version(),
        method=__doc__, counts=dict(counts), seconds=time.perf_counter() - started,
        corpus_sha256=sha256(raw_corpus).hexdigest(),
        audit_sha256=sha256(raw_audit).hexdigest(),
        source_sha256={name: sha256((fast / 'fastunknot' / name).read_bytes()).hexdigest()
                       for name in ['normal_sector.py', 'normal_surface_geometry.py',
                                    'sector_planar.py']},
        driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), cases=cases,
        interpretation='Exact normalized maxima and sign equivalence. Not an '
                       'implementation or timing of the O(t+k^2) proposed precheck.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('PASS', dict(counts), 'seconds', result['seconds'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, default=ROOT / 'code')
    parser.add_argument('--audit', type=Path, default=ROOT / 'results/corpus_audit.json')
    parser.add_argument('--corpus', type=Path, default=ROOT / 'fixtures/discovery_corpus.json')
    parser.add_argument('--output', type=Path, default=ROOT / 'results/euler_corner_audit.json')
    run(parser.parse_args())
