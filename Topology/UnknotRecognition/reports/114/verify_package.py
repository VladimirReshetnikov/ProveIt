#!/usr/bin/env python3
"""Verify delivered file integrity and cross-linked frozen research evidence.

Standard library only. This checks hashes and recorded consistency; it does
not prove mathematics, replace certificate replay, or authenticate an author.
Run before modifying or regenerating any delivered files.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT/name).read_text())

def main():
    entries = []
    for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT/name
        require(path.is_relative_to(ROOT) and '..' not in Path(name).parts,
                'invalid manifest path: ' + name)
        require(path.is_file(), 'missing file: ' + name)
        require(sha(path) == expected, 'changed file: ' + name)
        entries.append(name)
    require(len(entries) == len(set(entries)), 'duplicate manifest entry')
    provenance = read('PROVENANCE.json')
    require(sha(ROOT/'integration.patch') == provenance['patch_sha256'], 'patch mismatch')
    prefix = 'Topology/UnknotRecognition/fast/'
    for name, expected in provenance['changed_files'].items():
        require(name.startswith(prefix), 'unexpected changed path: ' + name)
        require(sha(ROOT/'code/fast'/name[len(prefix):]) == expected,
                'snapshot differs from patch source: ' + name)

    algebra = read('results/algebra_audit.json')
    require(algebra['passed'] and not algebra['production_files_changed_during_run'],
            'algebra audit did not pass on frozen sources')
    require(not algebra['decision_discrepancies'] and not algebra['certificate_failures']
            and not algebra['compiler_failures'] and not algebra['corruption_failures'],
            'algebra audit reports a discrepancy')
    counts = algebra['counts']
    decisions = sum(counts[k] for k in ['exhaustive_single', 'exhaustive_pair',
                                        'random_unstructured', 'random_positive', 'controls'])
    require(decisions == 8486 and counts['positive_certificates_checked'] == 1284,
            'unexpected algebra coverage')
    require(sha(ROOT/'experiments/algebra/audit_cyclic_basis.py') == algebra['audit_script_sha256'],
            'algebra audit script mismatch')
    compression = read('results/compression.json')
    for bank in [algebra, compression]:
        for name, expected in bank['production_sha256'].items():
            require(sha(ROOT/'code/fast/fastunknot'/name) == expected,
                    'measured production source mismatch: ' + name)
    require(all(r['status'] == 'COMPLETE' and r['verified'] for r in compression['results']),
            'incomplete compression result')
    implementation = read('results/native_implementation_audit.json')
    for name, expected in implementation['files'].items():
        require(sha(ROOT/'code/fast'/name) == expected, 'native source mismatch: ' + name)

    native = read('results/native_replay.json')
    require(len(native['records']) == 5, 'unexpected native record count')
    require(sha(ROOT/'code/fast/signed_annulus_research/corpus.json') == native['fixture_sha256']
            == provenance['fixture_sha256'], 'native fixture mismatch')
    native_hashes = {}
    for record in native['records']:
        certificate = read('results/' + record['certificate_path'])
        canonical = json.dumps(certificate, sort_keys=True, separators=(',', ':')).encode()
        require(hashlib.sha256(canonical).hexdigest() == record['certificate_sha256'],
                'native canonical certificate hash mismatch: ' + record['id'])
        require(len(canonical) == record['certificate_bytes'], 'native certificate length mismatch')
        require(record['old_status'] == 'INCONCLUSIVE' and record['new_status'] == 'COMPLETE'
                and record['replayed'], 'native status mismatch')
        require(record['census']['histogram'] == record['regina']['histogram']
                == [{'genus': 2, 'multiplicity': 2}], 'native genus mismatch')
        native_hashes[record['id']] = record['certificate_sha256']
    require({r['id']: r['certificate_sha256'] for r in read('results/native_replay_final.json')['records']}
            == native_hashes, 'native repeat changed certificates')

    exploration = read('results/exploration_summary.json')
    for name, expected in exploration['scripts'].items():
        require(sha(ROOT/'experiments/exploration/original'/name) == expected,
                'exploration script mismatch: ' + name)
    for name, evidence in exploration['experiments'].items():
        require(sha(ROOT/'experiments/exploration/recorded'/(name+'.log')) == evidence['log_sha256'],
                'exploration log mismatch: ' + name)
    require(set(exploration['common_primitive_hits']) == set(native_hashes), 'native exploration mismatch')

    regression = read('results/regression_audit.json')
    require(regression['final_coverage']['collected_tests'] == 1741
            and regression['final_coverage']['all_passed_across_full_run_and_targeted_rerun']
            and not regression['final_coverage']['single_clean_full_invocation_claimed'],
            'unexpected regression claim')
    for key in ['initial_full_run', 'failed_test_recheck', 'clean_full_run', 'fixture_test_recheck']:
        record = regression[key]
        require(sha(ROOT/'results/logs'/record['log']) == record['log_sha256'],
                'regression log mismatch: ' + key)
    print(json.dumps(dict(status='PASS', manifest_files=len(entries),
                          changed_sources=len(provenance['changed_files']),
                          native_certificates=len(native_hashes),
                          algebra_decisions=decisions,
                          compressed_benchmark_cases=len(compression['results']),
                          repository_tests_covered=1741), indent=2))

if __name__ == '__main__':
    main()
