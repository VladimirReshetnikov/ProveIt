"""Pinned baseline versus integrated native cuts; independent Regina checks.

Run from fast/: python -m source_core_dual_research.audit --output DIRECTORY
The frozen baseline is loaded from git at the declared source revision.  The
only changed entry points are the source-three-handle producer and v6 replay.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import types

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


PIN = '8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=20)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    args.output.mkdir(parents=True, exist_ok=True)
    packets = args.output / 'certificates'
    packets.mkdir(exist_ok=True)
    source = subprocess.check_output(['git', 'show',
        PIN + ':Topology/UnknotRecognition/fast/fastunknot/normal_cut_handlebodies.py'],
        cwd=root.parents[2])
    baseline = types.ModuleType('fastunknot._source_dual_baseline')
    baseline.__package__ = 'fastunknot'
    exec(compile(source, 'pinned_normal_cut_handlebodies.py', 'exec'), baseline.__dict__)
    corpus_bytes = (root / 'marked_parallelity_research/corpus.json').read_bytes()
    corpus = json.loads(corpus_bytes)
    results, counts = [], Counter()
    start = time.perf_counter()
    for index, case in enumerate(corpus['cases']):
        raw, rows = case['triangulation'], case['coordinates']
        at = time.perf_counter()
        old = baseline.normal_cut_handlebodies(raw, rows, record_certificate=True)
        baseline_time = time.perf_counter() - at
        at = time.perf_counter()
        new = normal_cut_handlebodies(raw, rows, record_certificate=True)
        native_time = time.perf_counter() - at
        counts['baseline_' + old['status']] += 1
        counts['new_' + new['status']] += 1
        if new['status'] != 'COMPLETE':
            counts['inconclusive_' + new['reason']] += 1
        record = dict(id=case['id'], baseline_status=old['status'],
            baseline_reason=old.get('reason'), native_status=new['status'],
            native_reason=new.get('reason'), baseline_seconds=baseline_time,
            native_seconds=native_time)
        if old['status'] == 'COMPLETE':
            assert new['status'] == 'COMPLETE', case['id']
            assert old['census'] == new['census'], case['id']
            counts['preserved_complete_censuses'] += 1
        if new['status'] == 'COMPLETE':
            at = time.perf_counter()
            assert verify_normal_cut_handlebodies(raw, rows, new['certificate']), case['id']
            record['replay_seconds'] = time.perf_counter() - at
            proof_bytes = json.dumps(json_safe(new['certificate']), sort_keys=True).encode()
            record.update(census=new['census'], certificate_bytes=len(proof_bytes),
                          certificate_sha256=hashlib.sha256(proof_bytes).hexdigest())
            counts['independent_replays'] += 1
        if old['status'] != 'COMPLETE' and new['status'] == 'COMPLETE':
            counts['new_certified_cases'] += 1
            name = case['id'].replace('/', '__')
            packet = dict(id=case['id'], triangulation=raw, coordinates=rows,
                          certificate=new['certificate'])
            (packets / (name + '.json')).write_text(json.dumps(json_safe(packet), indent=2) + '\n')
            record['dual_statistics'] = new['stats']['dual_core']
            try:
                oracle = subprocess.run([sys.executable, '-m',
                    'marked_parallelity_research.audit_census', '--oracle'],
                    cwd=root, input=json.dumps(case), text=True,
                    capture_output=True, timeout=args.timeout, check=True)
                reference = json.loads(oracle.stdout)
                record['regina'] = reference
                assert new['census']['histogram'] == reference['histogram'], case['id']
                counts['new_regina_agreements'] += 1
            except subprocess.TimeoutExpired:
                record['regina'] = dict(status='TIMEOUT', seconds=args.timeout)
        results.append(record)
        if (index + 1) % 10 == 0:
            print(json.dumps(dict(done=index + 1, counts=counts)), flush=True)
    report = dict(source_revision=PIN,
        baseline_entry_sha256=hashlib.sha256(source).hexdigest(),
        corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(), counts=counts,
        seconds=time.perf_counter() - start, cases=results)
    (args.output / 'native_audit.json').write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'])), flush=True)


if __name__ == '__main__':
    main()
