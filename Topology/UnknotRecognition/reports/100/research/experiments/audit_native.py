"""Reproduce source-bound native cut classification and independent replay.

Run with PYTHONPATH pointing at the selected fast/ runtime. Timings in this
coverage audit are diagnostic; the paired benchmark is a separate experiment.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--corpus', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--label', required=True)
    parser.add_argument('--strategy', choices=('bfs', 'max_weight', 'disabled'))
    parser.add_argument('--certificates')
    args = parser.parse_args()
    path = Path(args.corpus)
    bank = json.loads(path.read_text())['cases']
    records, counts = [], Counter()
    report = dict(label=args.label, strategy=args.strategy,
                  python=sys.version, platform=platform.platform(),
                  corpus_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  records=records)
    large_saved = 0
    for index, case in enumerate(bank):
        raw, rows = case['triangulation'], case['coordinates']
        kwargs = dict(record_certificate=True)
        if args.strategy is not None:
            kwargs['dual_strategy'] = args.strategy
        start = time.perf_counter()
        result = normal_cut_handlebodies(raw, rows, **kwargs)
        produced = time.perf_counter()
        verified = None
        if result['status'] == 'COMPLETE':
            verified = verify_normal_cut_handlebodies(raw, rows, result['certificate'])
            if not verified:
                raise AssertionError(('certificate replay failed', index, case['id']))
        end = time.perf_counter()
        record = dict(index=index, id=case['id'], status=result['status'],
                      reason=result.get('reason'), replay=verified,
                      produce_seconds=produced-start, replay_seconds=end-produced,
                      stats=result['stats'])
        if 'census' in result:
            record['histogram'] = result['census']['histogram']
            record['schema'] = result['certificate']['schema']
        weight = sum(encoded_integer(x) for row in rows for x in row)
        record['normal_weight_bits'] = weight.bit_length()
        is_dual = 'dual' in result['stats']
        if args.certificates and 'certificate' in result and (
                is_dual or index == 0 or (weight > 4096 and large_saved < 2)):
            if weight > 4096:
                large_saved += 1
            directory = Path(args.certificates)
            directory.mkdir(parents=True, exist_ok=True)
            packet = dict(case=case, result=result)
            name = f'{args.label}_{index:03d}.json'
            (directory/name).write_text(json.dumps(json_safe(packet), indent=2)+'\n')
            record['saved_certificate'] = name
        counts[result['status']] += 1
        if result.get('reason'):
            counts[result['reason']] += 1
        records.append(record)
        report['counts'] = dict(counts)
        Path(args.output).write_text(json.dumps(json_safe(report), indent=2)+'\n')
        print(json.dumps({k: record[k] for k in ('index', 'id', 'status', 'reason', 'replay')}),
              flush=True)
    print(json.dumps({'counts': dict(counts)}), flush=True)


if __name__ == '__main__':
    main()
