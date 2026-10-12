"""Reproduce the opt-in saturated source census on the maintained 106 cases."""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from unittest.mock import patch

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('reproduced/saturated/audit.json'))
    parser.add_argument('--fresh-oracles', action='store_true')
    parser.add_argument('--checkout', type=Path,
                        default=os.environ.get('PROVEIT_CHECKOUT'),
                        help='Patched ProveIt checkout; defaults to PROVEIT_CHECKOUT.')
    args = parser.parse_args()
    if args.checkout is None:
        parser.error('Set PROVEIT_CHECKOUT or pass --checkout pointing to the patched ProveIt checkout.')
    checkout = args.checkout.expanduser().resolve()
    fast = checkout / 'Topology/UnknotRecognition/fast'
    if not (fast / 'fastunknot/normal_cut_saturated.py').is_file():
        parser.error('The checkout must contain the accompanying saturated-bundle source changes.')
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe, certificate_equal
    from fastunknot.normal_cut_saturated import normal_cut_saturated
    from fastunknot.normal_cut_saturated_verify import verify_normal_cut_saturated
    corpus_path = fast / 'marked_parallelity_research/corpus.json'
    source = corpus_path.read_bytes()
    dependencies = [fast / 'fastunknot' / name for name in (
        'normal_cut_saturated.py', 'normal_cut_saturated_verify.py',
        'core_handlebody.py', 'column_cancellation_verify.py')]
    source_pins = {str(p.relative_to(checkout)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in dependencies}
    cases = json.loads(source)['cases']
    baseline_path = checkout / 'Topology/UnknotRecognition/synthesis/data/primitive-annuli-audit.json'
    baseline = {c['id']: c for c in json.loads(baseline_path.read_text())['cases']}
    out = args.output.parent
    (out / 'certificates').mkdir(parents=True, exist_ok=True)
    counts, records = Counter(), []
    started = time.perf_counter()
    for index, case in enumerate(cases):
        start = time.perf_counter()
        result = normal_cut_saturated(case['triangulation'], case['coordinates'],
                                      record_certificate=True)
        seconds = time.perf_counter()-start
        old = baseline[case['id']]
        record = dict(id=case['id'], status=result['status'], reason=result.get('reason'),
                      seconds=seconds, baseline_status=old['native_status'],
                      baseline_reason=old.get('native_reason'), stats=result['stats'])
        counts[result['status']] += 1
        if result['status'] == 'COMPLETE':
            proof = result['certificate']
            begin = time.perf_counter()
            with patch('fastunknot.normal_cut_saturated.normal_cut_saturated',
                       side_effect=AssertionError('producer invoked during replay')):
                with patch('fastunknot.normal_cut_saturated.saturated_source_census',
                           side_effect=AssertionError('finite producer invoked during replay')):
                    assert verify_normal_cut_saturated(case['triangulation'], case['coordinates'], proof)
            record['replay_seconds'] = time.perf_counter()-begin
            counts['independent_replays'] += 1
            record['census'] = result['census']
            if old['native_status'] == 'COMPLETE':
                assert certificate_equal(old['census']['histogram'], result['census']['histogram']), case['id']
                counts['prior_successes_retained'] += 1
            else:
                counts['new_successes'] += 1
                filename = f'{index:03d}.json'
                (out / 'certificates' / filename).write_text(json.dumps(json_safe(dict(
                    id=case['id'], triangulation=case['triangulation'], coordinates=case['coordinates'],
                    certificate=proof)), sort_keys=True, indent=2)+'\n')
                record['saved_certificate'] = 'certificates/'+filename
            profiles = proof['parallelity']['summary']['base_profiles']
            record['saturated_nondisk_profiles'] = [r['base_profile'] for r in proof['finite']['saturated_bases']
                if profiles[r['base_profile']]['euler_characteristic'] != 1]
            if record['saturated_nondisk_profiles']:
                counts['successes_with_saturated_nondisk_base'] += 1
        else:
            assert old['native_status'] != 'COMPLETE', case['id']
            counts[result['reason']] += 1
        reference = old.get('regina', {})
        if args.fresh_oracles:
            command = [sys.executable, '-m', 'marked_parallelity_research.audit_census', '--oracle']
            process = subprocess.run(command, input=json.dumps(case), text=True,
                capture_output=True, cwd=fast, timeout=15)
            if process.returncode:
                raise RuntimeError(process.stderr)
            reference = json.loads(process.stdout)
            counts['fresh_oracle_invocations'] += 1
        record['regina'] = reference
        if 'histogram' in reference:
            counts['regina_complete'] += 1
            if result['status'] == 'COMPLETE':
                assert result['census']['histogram'] == reference['histogram'], case['id']
                counts['regina_agreements'] += 1
                if old['native_status'] != 'COMPLETE':
                    counts['new_success_regina_agreements'] += 1
        else:
            counts['regina_not_expanded'] += 1
        records.append(record)
        if (index+1) % 10 == 0 or index+1 == len(cases):
            print(json.dumps(dict(done=index+1, counts=counts)), flush=True)
            args.output.with_name('audit.partial.json').write_text(json.dumps(json_safe(dict(
                counts=counts, cases=records, native_changed_source_sha256=source_pins)), indent=2)+'\n')
    report = dict(repository_pin='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
        corpus_sha256=hashlib.sha256(source).hexdigest(),
        baseline_sha256=hashlib.sha256(baseline_path.read_bytes()).hexdigest(),
        native_changed_source_sha256=source_pins,
        fresh_oracles=args.fresh_oracles, seconds=time.perf_counter()-started,
        counts=counts, cases=records)
    assert source_pins == {str(p.relative_to(checkout)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in dependencies}, 'native sources changed during audit'
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output), counts=counts)), flush=True)


if __name__ == '__main__':
    main()
