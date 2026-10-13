#!/usr/bin/env python3
"""Audit the benchmark families without importing any topology implementation.

The family constructors and their geometric identities are documented in the
article. This checker evaluates those identities, checks all recorded result
hashes, and compares retained JSON proof summaries. It does not replay the
geometric certificates (the separate certificate audit does that).
"""
import argparse
import hashlib
import json
from pathlib import Path


def integer(value):
    if type(value) is int:
        return value
    if isinstance(value, str) and value.lower().lstrip('+-').startswith('0x'):
        return int(value, 16)
    raise ValueError('invalid exact integer field')


def transport(value):
    if type(value) is int:
        return hex(value) if value.bit_length() > 4096 else value
    if isinstance(value, dict):
        return {key: transport(item) for key, item in value.items()}
    if isinstance(value, list):
        return [transport(item) for item in value]
    return value


def canonical(value):
    return json.dumps(transport(value), sort_keys=True, separators=(',', ':')).encode()


def row(chi, boundary, orientable, count):
    result = dict(chi=chi, boundary_components=boundary,
                  orientable=orientable, multiplicity=count)
    result['genus' if orientable else 'crosscaps'] = (
        (2 - chi - boundary) // 2 if orientable else 2 - chi - boundary)
    return result


def expected(source):
    family = source['family']
    if family == 'layered_meridian':
        return [row(1, 1, True, 1)]
    g = integer(source['parameters']['factor'])
    rows = [row(1, 1, True, g + 1)]
    if family == 'large_quadrilateral_content':
        assert g == 1 << source['parameters']['exponent_bits']
        return [row(1, 1, True, 2 * g + 1)]
    if family in ('one_sided_with_boundary', 'mixed_vertex_links'):
        rows.append(row(0, 2, True, g // 2))
        if g % 2:
            rows.append(row(0, 1, False, 1))
        if family == 'mixed_vertex_links':
            rows.append(row(2, 0, True, g + 2))
    elif family == 'closed_one_sided_zero_signature':
        rows.append(row(0, 0, True, g // 2))
        if g % 2:
            rows.append(row(0, 0, False, 1))
    else:
        raise ValueError('unrecognized family: ' + family)
    return sorted(rows, key=lambda r: (r['chi'], r['boundary_components'], not r['orientable']))


def decoded_rows(rows):
    return [{key: value if key == 'orientable' else integer(value)
             for key, value in record.items()} for record in rows]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('benchmark', type=Path)
    parser.add_argument('--proofs', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.benchmark.read_bytes()
    data = json.loads(raw)
    assert data['sources_unchanged']
    assert data['source_hashes_before'] == data['source_hashes_after']
    checks = []
    sample_count = proof_count = 0
    for case in data['cases']:
        name = case['source']['name']
        rows = expected(case['source'])
        assert decoded_rows(case['expected_topology_spectrum']) == rows, name
        digest = hashlib.sha256(canonical(rows)).hexdigest()
        for round_record in [case['warmup']] + case['rounds']:
            for arm, sample in round_record['samples'].items():
                assert sample['status'] == 'COMPLETE', (name, arm)
                assert sample['spectrum_sha256'] == digest, (name, arm)
                sample_count += 1
        proof_hashes = {}
        if args.proofs:
            for arm in data['arms']:
                path = args.proofs / name / (arm + '.json')
                proof_raw = path.read_bytes()
                proof = json.loads(proof_raw)
                supplied = (proof['topology_spectrum'] if arm == 'coordinates_reference'
                            else proof['summary']['topology_spectrum'])
                assert decoded_rows(supplied) == rows, (name, arm)
                digest_proof = hashlib.sha256(proof_raw.rstrip(b'\n')).hexdigest()
                assert digest_proof == case['warmup']['samples'][arm]['certificate_sha256']
                proof_hashes[arm] = digest_proof
                proof_count += 1
        checks.append(dict(case=name, family=case['source']['family'],
                           formula_spectrum=transport(rows), spectrum_sha256=digest,
                           retained_proof_sha256=proof_hashes))
    report = dict(schema='normal-topology-benchmark-formula-audit-v1',
                  benchmark_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  topology_implementation_imports=False,
                  cases=len(checks), exact_result_hash_matches=sample_count,
                  retained_proof_summary_matches=proof_count,
                  failures=0, success=True, checks=checks)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(json.dumps(report, indent=2).encode() + b'\n')
    print(json.dumps({key: report[key] for key in ('cases', 'exact_result_hash_matches',
          'retained_proof_summary_matches', 'failures', 'success')}))


if __name__ == '__main__':
    main()
