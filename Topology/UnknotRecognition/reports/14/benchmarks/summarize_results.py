#!/usr/bin/env python3
"""Rebuild summary CSV/JSON and audit the before/after lazy-pass comparison."""
import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_summary(result):
    rows = []
    for case in result['cases']:
        a = case['summary']['component']
        b = case['summary']['fitting_exact']
        d = case['summary']['fitting_decision']
        dp = case['summary']['fitting_decision_dp']
        row = dict(name=case['name'], n=case['crossings'])
        for key, backend in [('component_ms', a), ('fitting_ms', b),
                             ('decision_ms', d), ('dp_total_ms', dp)]:
            row[key] = 1000 * backend['median_seconds'] if backend.get('completed') else None
        for key, backend, metric in [
            ('component_entries', a, 'entries'), ('fitting_entries', b, 'entries'),
            ('component_compositions', a, 'compositions'), ('fitting_compositions', b, 'compositions'),
            ('old_largest', a, 'max_component_objects'), ('new_largest', b, 'max_component_objects'),
            ('fitting_splits', b, 'fitting_splits'), ('barcode_components', b, 'barcode_components'),
            ('checkpoint_count', d, 'interval_checkpoint_count'),
            ('max_checkpoint_gap', d, 'max_checkpoint_gap'), ('max_boundary', d, 'max_boundary')]:
            row[key] = backend.get('stats', {}).get(metric)
        rows.append(row)
    return rows


def compare(before, after):
    old = {case['name']: case for case in before['cases']}
    metrics = ['entries', 'compositions', 'fitting_splits', 'barcode_components', 'max_component_objects']
    backends = ['component', 'fitting_exact', 'fitting_decision', 'fitting_decision_dp']
    differences = []
    result_checks = stat_checks = 0
    for case in after['cases']:
        previous = old.get(case['name'])
        if previous is None:
            differences.append(dict(case=case['name'], missing='before'))
            continue
        for backend in backends:
            a, b = previous['summary'][backend], case['summary'][backend]
            if not a.get('completed') or not b.get('completed'):
                differences.append(dict(case=case['name'], backend=backend, incomplete=True))
                continue
            result_checks += 1
            if a['result'] != b['result']:
                differences.append(dict(case=case['name'], backend=backend, field='result',
                                        before=a['result'], after=b['result']))
            for metric in metrics:
                stat_checks += 1
                if a['stats'].get(metric) != b['stats'].get(metric):
                    differences.append(dict(case=case['name'], backend=backend, field=metric,
                        before=a['stats'].get(metric), after=b['stats'].get(metric)))
    return dict(backends=backends, metrics=metrics, result_comparisons=result_checks,
                deterministic_stat_comparisons=stat_checks, differences=differences,
                all_compared_results_and_stats_equal=not differences)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE / 'paired_results.json')
    parser.add_argument('--before', type=Path, default=HERE / 'paired_results_before_lazy.json')
    args = parser.parse_args()
    result = json.loads(args.input.read_text())
    rows = make_summary(result)
    args.input.with_name('summary.json').write_text(json.dumps(rows, indent=2) + '\n')
    with args.input.with_name('summary.csv').open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]) if rows else ['name'])
        writer.writeheader()
        writer.writerows(rows)
    audit = dict(utc=datetime.now(timezone.utc).isoformat(), final_file=args.input.name,
                 final_sha256=digest(args.input), cases=len(result['cases']),
                 source_unchanged_during_final_run=result['source_unchanged_during_run'])
    runs = [run for case in result['cases'] for run in case['runs']]
    audit.update(calls=len(runs), completed=sum(run['outcome'] == 'completed' for run in runs),
                 limits=[dict(case=case['name'], backend=run['backend'], repetition=run['repetition'],
                              reason=run['reason']) for case in result['cases'] for run in case['runs']
                         if run['outcome'] != 'completed'])
    if args.before.is_file():
        audit.update(before_file=args.before.name, before_sha256=digest(args.before),
                     lazy_comparison=compare(json.loads(args.before.read_text()), result))
    expected_agreement = True
    for case in result['cases']:
        exact = {s['result']['rank'] for s in case['summary'].values()
                 if s.get('completed') and 'rank' in s['result']}
        capped = {s['result']['rank_capped'] for s in case['summary'].values()
                  if s.get('completed') and 'rank_capped' in s['result']}
        expected_agreement &= len(exact) <= 1
        if exact:
            expected_agreement &= capped <= {min(3, next(iter(exact)))}
    audit['all_completed_exact_and_capped_results_agree'] = expected_agreement
    args.input.with_name('benchmark_audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    print(json.dumps(audit, indent=2))
    if not expected_agreement or audit.get('lazy_comparison', {}).get('differences'):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
