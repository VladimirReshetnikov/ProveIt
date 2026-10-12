"""Reproducible whole-cut audit; imports one requested source tree per process.

Run this file with --fast-dir PATH --output JSON.  It compares every complete
answer against the committed reference histogram and independently replays
all emitted proofs.  --oracle-top reruns Regina on the ten formerly excluded
three-handle cases, with per-case subprocess timeouts.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--oracle-top', action='store_true')
    parser.add_argument('--save-certificates', type=Path)
    args = parser.parse_args()
    args.fast_dir = args.fast_dir.resolve()
    sys.path.insert(0, str(args.fast_dir))
    from fastunknot.integer_codec import json_safe, certificate_equal
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    corpus_path = args.fast_dir / 'marked_parallelity_research/corpus.json'
    corpus_bytes = corpus_path.read_bytes()
    bank = json.loads(corpus_bytes)['cases']
    reference = {r['id']: r for r in json.loads(args.reference.read_text())['cases']}
    counts, results = Counter(), []
    start = time.perf_counter()
    if args.save_certificates:
        args.save_certificates.mkdir(parents=True, exist_ok=True)
    for case in bank:
        initial = time.perf_counter()
        result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                        record_certificate=True)
        produced = time.perf_counter()
        rec = dict(id=case['id'], status=result['status'], reason=result.get('reason'),
                   produce_seconds=produced-initial)
        counts[result['status']] += 1
        old = reference[case['id']]
        was_top = old.get('native_reason') == 'core_has_three_handles'
        if result['status'] == 'COMPLETE':
            assert verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                                  result['certificate']), case['id']
            rec['replay_seconds'] = time.perf_counter()-produced
            rec['histogram'] = result['census']['histogram']
            rec['schema'] = result['certificate']['schema']
            encoded = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
            rec['certificate_bytes'] = len(encoded)
            rec['certificate_sha256'] = hashlib.sha256(encoded).hexdigest()
            counts['independent_replays'] += 1
            if 'histogram' in old.get('regina', {}):
                assert rec['histogram'] == old['regina']['histogram'], case['id']
                counts['stored_oracle_agreements'] += 1
            if old['native_status'] == 'COMPLETE':
                assert certificate_equal(old['census']['histogram'], rec['histogram']), case['id']
                counts['old_successes_preserved'] += 1
            else:
                counts['new_successes'] += 1
                if args.save_certificates:
                    filename = case['id'].replace('/', '__') + '.json'
                    payload = dict(case=case, certificate=result['certificate'])
                    (args.save_certificates/filename).write_text(
                        json.dumps(json_safe(payload), indent=2)+'\n')
        else:
            counts['inconclusive_'+result['reason']] += 1
            assert old['native_status'] != 'COMPLETE', ('coverage regression', case['id'])
        if was_top:
            rec['top_reduction'] = result['stats'].get('top_reduction')
        if args.oracle_top and was_top:
            ran = subprocess.run([sys.executable, '-m',
                                  'marked_parallelity_research.audit_census', '--oracle'],
                                 cwd=args.fast_dir, input=json.dumps(case), text=True,
                                 capture_output=True, timeout=45, check=True)
            fresh = json.loads(ran.stdout)
            rec['fresh_regina'] = fresh
            assert fresh['histogram'] == old['regina']['histogram'], case['id']
            if result['status'] == 'COMPLETE':
                assert rec['histogram'] == fresh['histogram'], case['id']
            counts['fresh_top_oracles'] += 1
        results.append(rec)
    import regina
    report = dict(python=sys.version, platform=platform.platform(),
                  regina=regina.versionString(), fast_dir=str(args.fast_dir),
                  corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(),
                  counts=counts, seconds=time.perf_counter()-start, cases=results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'])), flush=True)


if __name__ == '__main__':
    main()
