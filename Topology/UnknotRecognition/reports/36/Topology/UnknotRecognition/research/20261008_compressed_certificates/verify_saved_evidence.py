#!/usr/bin/env python3
"""Verify the saved research evidence without Regina or benchmark reruns.

Run this file from any working directory.  Paths are resolved relative to its
own location.  The script checks recorded source hashes and input hashes,
replays all eleven supplied normal-disc certificates, verifies their exact
Fibonacci disc counts, independently enumerates the twelve tiny gluing orbit
records, and recomputes saved completion counts and knot-corpus agreement.
It checks the saved knot certificate digests; it does not regenerate those
certificates or promote relative geometric evidence to knot verdicts.

Optional: --output PATH also saves the JSON verification summary.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
from statistics import median
import sys


PROJECT = Path(__file__).resolve().parents[2]
FAST = PROJECT / 'fast'
NORMAL = FAST / 'certificate_research' / 'results'
SIZES = (1, 2, 6, 10, 14, 18, 22, 32, 64, 128, 256)
KNOT_NAMES = {f'survivor-{i:02d}' for i in range(12)} | {'mirror-03', 'mirror-08', 'gordian'}
ENDPOINT_SOURCES = {
    'endpoint_research/baseline_compressed_lcs.py',
    'fastunknot/compressed_endpoint.py',
    'fastunknot/compressed_lcs.py',
    'fastunknot/compressed_words.py',
    'benchmark_compressed_endpoint.py',
}


class EvidenceError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def read_json(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_path(relative):
    """Recorded source maps must stay within the delivered fast/ tree."""
    require(isinstance(relative, str), 'source path must be a string')
    path = Path(relative)
    require(not path.is_absolute(), f'absolute recorded source path: {relative}')
    resolved = (FAST / path).resolve()
    require(resolved.is_relative_to(FAST.resolve()), f'source path escapes fast/: {relative}')
    return resolved


def verify_sources(study):
    hashes = study['source_sha256']
    require(ENDPOINT_SOURCES <= set(hashes), 'an endpoint source digest is missing')
    mapping = study.get('source_archive_map', {})
    require(set(mapping) <= set(hashes), 'archive map contains an unrecorded source')
    checked = []
    for original, expected in sorted(hashes.items()):
        actual_path = mapping.get(original, original)
        require(digest(checked_path(actual_path)) == expected,
                f'source SHA256 mismatch: {original} -> {actual_path}')
        checked.append({'recorded_path': original, 'verified_path': actual_path,
                        'sha256': expected})
    return checked


def completion_summary(study, section):
    rows = study[section]
    rounds = study['measured_rounds']
    require(type(rounds) is int and rounds > 0, 'invalid measured-round count')
    results = {'rows': len(rows), 'baseline_complete': 0, 'endpoint_complete': 0,
               'new_completions': 0, 'lost_completions': 0,
               'both_incomplete': 0, 'mixed_status_rows': []}
    identities = set()
    for row in rows:
        identity = row['family'], row['bits']
        require(identity not in identities, f'duplicate {section} row: {identity}')
        identities.add(identity)
        require(len(row['samples']) == rounds, f'wrong sample count: {identity}')
        complete = {}
        for arm in ('baseline', 'endpoint'):
            samples = [sample['measurements'][arm] for sample in row['samples']]
            states = {sample['status'] for sample in samples}
            require(states <= {'COMPLETE', 'LIMIT'}, f'unexpected status: {identity}, {arm}')
            complete[arm] = states == {'COMPLETE'}
            results[arm + '_complete'] += complete[arm]
            if len(states) > 1:
                results['mixed_status_rows'].append({'family': identity[0],
                    'bits': identity[1], 'arm': arm, 'statuses': sorted(states)})
            require(median(sample['seconds'] for sample in samples) == row['median_seconds'][arm],
                    f'saved median mismatch: {identity}, {arm}')
        results['new_completions'] += complete['endpoint'] and not complete['baseline']
        results['lost_completions'] += complete['baseline'] and not complete['endpoint']
        results['both_incomplete'] += not complete['baseline'] and not complete['endpoint']
    return results


def knot_summary(study):
    rows = study['rows']
    require(len(rows) == len(KNOT_NAMES) and {row['name'] for row in rows} == KNOT_NAMES,
            'saved knot corpus differs from the fifteen-case release corpus')
    paired, trials, hits = 0, 0, 0
    for row in rows:
        require(len(row['samples']) == study['measured_rounds'],
                f'wrong knot sample count: {row["name"]}')
        for sample in row['samples']:
            pair = sample['measurements']
            left, right = pair['baseline'], pair['endpoint']
            require(left['status'] == right['status'] == 'UNKNOT',
                    f'non-UNKNOT saved corpus outcome: {row["name"]}')
            require(left['method'] == right['method'], f'knot method differs: {row["name"]}')
            require(left['certificate_sha256'] == right['certificate_sha256'],
                    f'knot certificate digests differ: {row["name"]}')
            require(left['search_stats'] == right['search_stats'],
                    f'knot search statistics differ: {row["name"]}')
            for arm in ('baseline', 'endpoint'):
                stats = pair[arm]['search_stats'] or {}
                arm_trials = stats.get('lcs_endpoint_trials', 0)
                arm_hits = stats.get('lcs_endpoint_hits', 0)
                require(arm_trials == arm_hits == 0,
                        f'endpoint activated in saved knot corpus: {row["name"]}, {arm}')
                trials += arm_trials
                hits += arm_hits
            paired += 1
        for arm in ('baseline', 'endpoint'):
            require(median(sample['measurements'][arm]['seconds'] for sample in row['samples'])
                    == row['median_seconds'][arm], f'knot median mismatch: {row["name"]}, {arm}')
    return {'rows': len(rows), 'paired_measurements': paired,
            'saved_certificate_digests_identical': True,
            'saved_search_statistics_identical': True,
            'endpoint_trials': trials, 'endpoint_hits': hits,
            'sum_of_case_medians_seconds': {
                arm: sum(row['median_seconds'][arm] for row in rows)
                for arm in ('baseline', 'endpoint')}}


def verify_endpoint_studies():
    studies, result = {}, {}
    for name, filename in (
            ('rank', 'endpoint_ap_20261008.json'),
            ('lcp_ablation', 'endpoint_ap_lcp_ablation_20261008.json')):
        study = read_json(FAST / 'results' / filename)
        studies[name] = study
        require(('rank galloping' in study['variant']) if name == 'rank'
                else ('LCP clipping ablation' in study['variant']), f'wrong variant label: {filename}')
        result[name] = {'variant': study['variant'], 'source_hashes': verify_sources(study),
                        'kernels': completion_summary(study, 'kernels'),
                        'operations': completion_summary(study, 'operations'),
                        'knot_corpus': knot_summary(study)}
    old = {row['name']: row for row in studies['lcp_ablation']['rows']}
    for row in studies['rank']['rows']:
        require(row['pd'] == old[row['name']]['pd'], f'PD differs between studies: {row["name"]}')
        old_digests = {sample['measurements'][arm]['certificate_sha256']
                       for sample in old[row['name']]['samples'] for arm in ('baseline', 'endpoint')}
        new_digests = {sample['measurements'][arm]['certificate_sha256']
                       for sample in row['samples'] for arm in ('baseline', 'endpoint')}
        require(len(old_digests) == 1 and old_digests == new_digests,
                f'knot certificate differs between studies: {row["name"]}')
    result['same_knot_inputs_and_saved_certificate_digests_between_studies'] = True
    return result


def load_normal_checker():
    # This standalone module has only standard-library imports.  Loading it
    # directly avoids importing the recognition pipeline or optional engines.
    path = FAST / 'fastunknot' / 'normal_disk_certificate.py'
    spec = importlib.util.spec_from_file_location('_saved_normal_disk_checker', path)
    require(spec is not None and spec.loader is not None, 'cannot load normal-disc checker')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def fibonacci(index):
    left, right = 0, 1
    for _ in range(index):
        left, right = right, left + right
    return left


def verify_normal_fixtures():
    study = read_json(NORMAL / 'normal_disk_benchmark.json')
    rows = study['rows']
    require(len(rows) == len(SIZES) and {row['tetrahedra'] for row in rows} == set(SIZES),
            'normal fixture rows differ from the eleven-case release corpus')
    expected_files = {f'layered_torus_{size}.json' for size in SIZES}
    require({path.name for path in NORMAL.glob('layered_torus_*.json')} == expected_files,
            'normal fixture files do not match their recorded rows')
    checker, checked, completions = load_normal_checker(), [], Counter()
    attempts = Counter()
    for row in sorted(rows, key=lambda item: item['tetrahedra']):
        size = row['tetrahedra']
        path = NORMAL / f'layered_torus_{size}.json'
        encoded = path.read_bytes()
        require(hashlib.sha256(encoded).hexdigest() == row['sha256'], f'fixture SHA256 mismatch: {path.name}')
        require(len(encoded) == row['certificate_bytes'], f'fixture byte count mismatch: {path.name}')
        fixture = json.loads(encoded)
        evidence = checker.audit_normal_disk_certificate(fixture['triangulation'], fixture['certificate'])
        require(evidence == row['evidence'], f'replayed normal evidence differs: {path.name}')
        total = sum(sum(coords) for coords in fixture['certificate']['normal_coordinates'])
        expected = fibonacci(size + 5) - 5
        require(total == evidence['normal_disks'] == expected,
                f'normal disc count is not F_(t+5)-5: {path.name}')
        require(evidence['tetrahedra'] == size, f'wrong tetrahedron count: {path.name}')
        require(len(row['samples']) == study['measured_rounds'], f'normal sample count mismatch: {path.name}')
        arms = set(row['samples'][0]['results'])
        for sample in row['samples']:
            require(set(sample['results']) == arms, f'inconsistent normal benchmark arms: {path.name}')
        recorded_complete = {}
        expected_medians = {}
        for arm in arms:
            samples = [sample['results'][arm] for sample in row['samples']]
            count = sum(sample['status'] == 'COMPLETE' for sample in samples)
            recorded_complete[arm] = count
            completions[arm] += count
            attempts[arm] += len(samples)
            if count == len(samples):
                expected_medians[arm] = median(sample['seconds'] for sample in samples)
        require(recorded_complete == row['completed'], f'normal completion count mismatch: {path.name}')
        require(expected_medians == row['median_seconds'], f'normal median mismatch: {path.name}')
        checked.append({'fixture': str(path.relative_to(PROJECT)), 'sha256': row['sha256'],
                        'tetrahedra': size, 'normal_disks': total,
                        'fibonacci_identity': f'F_{size + 5} - 5',
                        'status': evidence['status']})
    return {'fixtures_checked': len(checked), 'checks': checked,
            'recorded_benchmark_completions': {
                arm: {'complete': completions[arm], 'attempts': attempts[arm]}
                for arm in sorted(attempts)},
            'scope': 'replayed relative compressing-disc certificates in the supplied triangulations'}


def literal_orbit_count(kind, modulus, beta):
    """Independent tiny simultaneous-conjugacy enumeration; at most 12 sheets."""
    elements = [(parity, shift) for parity in range(1 if kind == 'cyclic' else 2)
                for shift in range(modulus)]

    def multiply(left, right):
        parity, shift = left
        other_parity, other_shift = right
        return parity ^ other_parity, (shift + (-other_shift if parity else other_shift)) % modulus

    def inverse(value):
        parity, shift = value
        return parity, (shift if parity else -shift) % modulus

    unseen, count = set(product(elements, repeat=beta)), 0
    while unseen:
        representative = next(iter(unseen))
        orbit = {tuple(multiply(inverse(gauge), multiply(value, gauge))
                       for value in representative) for gauge in elements}
        unseen.difference_update(orbit)
        count += 1
    return len(elements) ** beta, count


def verify_gluing_records():
    study = read_json(FAST / 'results' / 'regular_cover_gluing_20261008.json')
    source = FAST / 'fastunknot' / 'regular_cover_gluing.py'
    require(digest(source) == study['code_sha256'], 'gluing implementation SHA256 mismatch')
    rows = study['audit']['phase_orbits']
    expected_keys = {(kind, modulus, 2) for kind in ('cyclic', 'dihedral') for modulus in range(1, 7)}
    require(len(rows) == len(expected_keys) and
            {(row['kind'], row['modulus'], row['cycle_rank']) for row in rows} == expected_keys,
            'gluing orbit records differ from the twelve tiny release cases')
    checked = []
    for row in rows:
        assignments, count = literal_orbit_count(row['kind'], row['modulus'], row['cycle_rank'])
        require(assignments == row['phase_assignments'], 'gluing phase-assignment count mismatch')
        require(count == row['literal_orbits'] == row['canonical_keys'],
                f'gluing orbit count mismatch: {row["kind"]}, m={row["modulus"]}')
        checked.append({'kind': row['kind'], 'modulus': row['modulus'],
                        'cycle_rank': row['cycle_rank'], 'phase_assignments': assignments,
                        'verified_orbits': count})
    return {'source': str(source.relative_to(PROJECT)), 'source_sha256': study['code_sha256'],
            'tiny_orbit_records_recomputed': len(checked), 'orbits': checked,
            'saved_large_benchmark_cases': len(study['benchmark']['cases'])}


def verify_saved_evidence():
    return {'status': 'VERIFIED_SAVED_EVIDENCE',
            'endpoint': verify_endpoint_studies(),
            'normal_disks': verify_normal_fixtures(),
            'gluing': verify_gluing_records(),
            'scope': 'saved evidence consistency, source/input hashes, and replayed relative normal-disc certificates; no timings rerun'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = verify_saved_evidence()
    except (EvidenceError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'status': 'FAILED', 'error': str(error)}, indent=2))
        return 1
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
