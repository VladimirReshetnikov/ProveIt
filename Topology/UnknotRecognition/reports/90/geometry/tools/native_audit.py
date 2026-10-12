"""Measure coverage on the retained source corpus and independently cut new cases."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

from unsaturated_bundles.finite import encode
from unsaturated_bundles.native import (
    normal_cut_unsaturated_handlebodies, verify_normal_cut_unsaturated_handlebodies)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--corpus', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--oracle-timeout', type=float, default=8.0)
    args = parser.parse_args()
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.integer_codec import json_safe
    import regina
    corpus_path = Path(args.corpus)
    corpus = json.loads(corpus_path.read_text())
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    counts, records = Counter(), []
    start = time.perf_counter()
    for case in corpus['cases']:
        raw, coordinates = case['triangulation'], case['coordinates']
        old = normal_cut_handlebodies(raw, coordinates, record_certificate=False)
        initial = time.perf_counter()
        new = normal_cut_unsaturated_handlebodies(raw, coordinates, record_certificate=True)
        produced = time.perf_counter()
        record = dict(id=case['id'], old_status=old['status'], old_reason=old.get('reason'),
                      new_status=new['status'], new_reason=new.get('reason'),
                      producer_seconds=produced - initial)
        counts['old_' + old['status']] += 1
        counts['new_' + new['status']] += 1
        if new['status'] == 'COMPLETE':
            assert verify_normal_cut_unsaturated_handlebodies(raw, coordinates, new['certificate'])
            record['replay_seconds'] = time.perf_counter() - produced
            record['histogram'] = new['census']['histogram']
            counts['source_replays'] += 1
        if old['status'] == 'COMPLETE':
            assert new['status'] == 'COMPLETE'
            assert old['census']['histogram'] == new['census']['histogram']
            counts['old_coverage_preserved'] += 1
        elif new['status'] == 'COMPLETE':
            counts['newly_covered'] += 1
            # Independent oracle starts from the actual face pairings and
            # coordinates, expands the cut, then recognises every component.
            completed = subprocess.run([sys.executable, '-m',
                'marked_parallelity_research.audit_census', '--oracle'],
                input=json.dumps(case), text=True, capture_output=True,
                timeout=args.oracle_timeout)
            if completed.returncode:
                raise RuntimeError(completed.stderr)
            oracle = json.loads(completed.stdout)
            assert oracle['histogram'] == new['census']['histogram']
            record['regina'] = oracle
            counts['newly_covered_regina_agreements'] += 1
            stem = case['id'].replace('/', '_')
            saved = dict(source=case, certificate=new['certificate'])
            target = output.parent / (stem + '_certificate.json')
            target.write_text(json.dumps(json_safe(saved), indent=2) + '\n')
            record['saved_certificate'] = target.name
        else:
            counts['remaining_' + new['reason']] += 1
        records.append(record)
        if len(records) % 10 == 0:
            print(json.dumps(dict(done=len(records), counts=counts)), flush=True)
    report = dict(scope='Source cut classification coverage, not end-to-end unknot speedup',
        corpus_sha256=hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
        corpus_source_revision=corpus.get('source_revision'), python=sys.version,
        platform=platform.platform(), regina=regina.versionString(), counts=dict(counts),
        seconds=time.perf_counter() - start, cases=records)
    output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'])), flush=True)


if __name__ == '__main__':
    main()
