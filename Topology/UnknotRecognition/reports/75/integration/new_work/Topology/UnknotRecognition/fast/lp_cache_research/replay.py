"""Replay saved genuine completed certificates without importing their producers.

From fast/: python -m lp_cache_research.replay --output lp_cache_research/replay_results.json

Synthetic algebraic certificates and genuine inconclusive cases are expressly
excluded from certificate replay. Their exclusion is recorded in the output.
The optional compact summary is checked against the saved raw measurements.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib
import json
from pathlib import Path
import sys
import time
from types import ModuleType


HERE = Path(__file__).resolve().parent
FAST = HERE.parent
PACKAGE = '_lp_certificate_replay'
FORBIDDEN = {'normal_propagation', 'normal_propagation_cached', 'exact_lp',
             'audit', 'synthetic_family'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def imported_producers():
    return sorted(name for name in sys.modules
                  if ((name.startswith(('fastunknot.', PACKAGE+'.', 'lp_cache_research.'))
                       and name.rsplit('.', 1)[-1] in FORBIDDEN)
                      or name == 'regina' or name.startswith('regina.')))


def independent_verifier():
    # Load the unmodified files under a private package namespace. This avoids
    # executing fastunknot/__init__.py, whose public API imports recognition
    # code unrelated to independent arithmetic certificate verification.
    package = ModuleType(PACKAGE)
    package.__path__ = [str(FAST/'fastunknot')]
    sys.modules[PACKAGE] = package
    verifier = importlib.import_module(PACKAGE+'.normal_propagation_verify')
    codec = importlib.import_module(PACKAGE+'.integer_codec')
    return verifier.verify_normal_propagation_certificate, codec.json_safe


def check_summary(summary, cases):
    require(summary.get('paired_cases') == len(cases), 'summary case count differs')
    require(summary.get('paired_samples') == sum(len(c['samples']) for c in cases),
            'summary paired-sample count differs')
    rows = summary.get('results', [])
    by_name = {row['name']: row for row in rows}
    require(len(by_name) == len(rows) == len(cases), 'duplicate or missing summary rows')
    require(set(by_name) == {case['name'] for case in cases}, 'summary case names differ')
    checked = 2
    for case in cases:
        sample = case['samples'][0]
        before, after = sample['baseline'], sample['screened']
        expected = dict(name=case['name'], kind=case['kind'],
                        baseline_status=before['status'], screened_status=after['status'],
                        median_seconds=case.get('median_search_seconds'),
                        median_speedup=case.get('median_speedup'),
                        complete_certificates_equal=sample.get('complete_certificates_equal'))
        if before.get('stats') is not None and after.get('stats') is not None:
            expected.update(baseline_lp_calls=before['stats']['lp_calls'],
                            screened_lp_calls=after['stats']['lp_calls'],
                            baseline_lp_pivots=before['stats']['lp_pivots'],
                            screened_lp_pivots=after['stats']['lp_pivots'],
                            local_hits=after['stats']['witness_local_hits'],
                            antichain_hits=after['stats']['witness_antichain_hits'])
        for key, value in expected.items():
            if key in by_name[case['name']]:
                require(by_name[case['name']][key] == value,
                        f'summary mismatch for {case["name"]}: {key}')
                checked += 1
    return dict(rows_checked=len(rows), values_checked=checked)


def replay(results_path, summary_path=None):
    require(not imported_producers(), 'run this replay in a fresh interpreter without producers')
    start = time.perf_counter()
    verify, json_safe = independent_verifier()

    def digest(value):
        return sha256(json.dumps(json_safe(value), sort_keys=True,
                                 separators=(',', ':')).encode()).hexdigest()

    raw_bytes = results_path.read_bytes()
    data = json.loads(raw_bytes)
    require(data.get('schema') == 'normal-propagation-witness-screening-audit-v1',
            'unexpected saved audit schema')
    cases = data['cases']
    require(len({case['name'] for case in cases}) == len(cases), 'duplicate saved case names')
    outcome = dict(schema='normal-propagation-independent-saved-replay-v1', status='PASSED',
                   generated_utc=datetime.now(timezone.utc).isoformat(),
                   results_file=results_path.name, results_sha256=sha256(raw_bytes).hexdigest(),
                   verified_certificates=[], genuine_cases_without_certificate=[],
                   excluded_algebraic_cases=[], genuine_input_digest_checks=0,
                   sample_certificate_digest_checks=0,
                   summary_validation=None, searches_run=0, native_constructors_run=0)
    complete_statuses = {'POSITIVE_EULER', 'NO_POSITIVE_EULER'}
    for case in cases:
        name = case['name']
        if case['kind'] == 'algebraic_cone':
            outcome['excluded_algebraic_cases'].append(name)
            continue
        require(case['kind'] == 'genuine_triangulation', f'unknown case kind: {name}')
        source = case['triangulation']
        require(digest(source) == case['input_sha256'], f'source digest mismatch: {name}')
        outcome['genuine_input_digest_checks'] += 1
        proof = case.get('certificate')
        if proof is None:
            require(all(sample[arm]['status'] not in complete_statuses
                        and sample[arm].get('certificate_sha256') is None
                        for sample in case['samples'] for arm in ('baseline', 'screened')),
                    f'completed measurement is missing its saved certificate: {name}')
            outcome['genuine_cases_without_certificate'].append(name)
            continue
        require(proof.get('status') in complete_statuses, f'invalid completed status: {name}')
        certificate_digest = digest(proof)
        for sample in case['samples']:
            if 'complete_certificates_equal' in sample:
                require(sample['complete_certificates_equal'] is True,
                        f'saved completed-pair equality flag is false: {name}')
            for arm in ('baseline', 'screened'):
                measurement = sample[arm]
                require(measurement['status'] == proof['status'],
                        f'measurement and certificate statuses differ: {name}/{arm}')
                require(measurement.get('certificate_sha256') == certificate_digest,
                        f'paired certificate digest mismatch: {name}/{arm}')
                outcome['sample_certificate_digest_checks'] += 1
        require(verify(source, proof), f'independent certificate replay rejected: {name}')
        outcome['verified_certificates'].append(dict(name=name, status=proof['status'],
                    source_sha256=case['input_sha256'], certificate_sha256=certificate_digest,
                    negative_anchor_trees=len(proof.get('anchor_trees', []))))
    if summary_path is not None and summary_path.exists():
        summary_bytes = summary_path.read_bytes()
        outcome['summary_validation'] = dict(check_summary(json.loads(summary_bytes), cases),
                                             file=summary_path.name,
                                             sha256=sha256(summary_bytes).hexdigest())
    dependencies = []
    for name, module in sorted(sys.modules.items()):
        if name.startswith(PACKAGE+'.') and getattr(module, '__file__', None):
            path = Path(module.__file__).resolve()
            relative = str(path.relative_to(FAST))
            file_digest = sha256(path.read_bytes()).hexdigest()
            if relative in data.get('source_sha256', {}):
                require(data['source_sha256'][relative] == file_digest,
                        f'verifier source differs from the saved audit pin: {relative}')
            dependencies.append(dict(path=relative, sha256=file_digest))
    outcome['unchanged_verifier_dependencies'] = dependencies
    outcome['producer_solver_or_native_modules_imported'] = imported_producers()
    require(not outcome['producer_solver_or_native_modules_imported'],
            'a producer, LP solver, or native constructor module was imported')
    outcome['genuine_completed_certificates_verified'] = len(outcome['verified_certificates'])
    outcome['positive_certificates_verified'] = sum(
        row['status'] == 'POSITIVE_EULER' for row in outcome['verified_certificates'])
    outcome['negative_certificates_verified'] = sum(
        row['status'] == 'NO_POSITIVE_EULER' for row in outcome['verified_certificates'])
    outcome['synthetic_certificates_replayed'] = 0
    outcome['replay_script_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    outcome['elapsed_seconds'] = time.perf_counter()-start
    return outcome


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, default=HERE/'results.json')
    parser.add_argument('--summary', type=Path, help='defaults to summary.json beside the results')
    parser.add_argument('--output', type=Path, help='save the replay report; otherwise print it')
    args = parser.parse_args()
    summary_path = args.summary or args.results.with_name('summary.json')
    if args.summary is not None and not args.summary.exists():
        parser.error('the explicitly requested summary file does not exist')
    outcome = replay(args.results, summary_path)
    wire = json.dumps(outcome, indent=2)+'\n'
    if args.output:
        args.output.write_text(wire)
    print(wire, end='')


if __name__ == '__main__':
    main()
