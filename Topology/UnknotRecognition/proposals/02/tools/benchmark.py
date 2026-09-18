"""Same-interpreter comparison against the unchanged supplied implementation.

Run from any directory: python tools/benchmark.py --limit 30 --repeats 3
A process wall timeout backs up the cooperative per-call deadline. Inputs and
imports are outside timed regions. Cache state is cold for every repetition.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def worker(job):
    wall_limit = (job['limit'] + 5) * job['repeats'] + 10
    try:
        p = subprocess.run([sys.executable, str(ROOT/'tools/worker.py')],
                           input=json.dumps(job), text=True, capture_output=True,
                           timeout=wall_limit)
    except subprocess.TimeoutExpired:
        return {'status': 'wall-limit', 'wall_limit_seconds': wall_limit,
                'answer': None, 'median_seconds': None, 'samples_seconds': []}
    if p.returncode:
        return {'status': 'error', 'stderr': p.stderr, 'answer': None,
                'median_seconds': None, 'samples_seconds': []}
    return json.loads(p.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=float, default=30)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--only', help='Optional substring of case ID')
    parser.add_argument('--output', type=Path, default=ROOT/'results/benchmark.json')
    args = parser.parse_args()
    if args.limit <= 0 or args.repeats < 1:
        parser.error('limit and repeats must be positive')
    cases = json.loads((ROOT/'tools/corpus.json').read_text())
    out = {'utc_start': datetime.now(timezone.utc).isoformat(),
           'python': sys.version, 'executable': sys.executable,
           'platform': platform.platform(), 'processor': platform.processor(),
           'cpu_count': os.cpu_count(), 'limit_seconds': args.limit, 'repeats': args.repeats,
           'timing': 'perf_counter; input construction/imports excluded; cold algebra caches; '
                     'separate process per engine and input; same host; sequential engines',
           'cases': []}
    try:
        out['cpu_model'] = next(x.split(':',1)[1].strip() for x in
                                Path('/proc/cpuinfo').read_text().splitlines()
                                if x.startswith('model name'))
    except (OSError, StopIteration):
        pass
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for index, case in enumerate(cases):
        if args.only and args.only not in case['id']:
            continue
        row = {k:v for k,v in case.items() if k != 'diagram'}
        engines = ('baseline','optimized') if index%2 == 0 else ('optimized','baseline')
        for engine in engines:
            job = {**case, 'engine':engine, 'limit':args.limit, 'repeats':args.repeats}
            row[engine] = worker(job)
            print(case['id'], engine, row[engine]['status'],
                  row[engine]['median_seconds'], flush=True)
        b, a = row['baseline'], row['optimized']
        if b['status'] == a['status'] == 'ok':
            row['speedup'] = b['median_seconds']/a['median_seconds']
            key = 'reduced_rank' if case['method']=='scan' else \
                  'status' if case['method']=='pipeline' else \
                  'order' if case['method']=='order' else 'remaining'
            row['agrees'] = b['answer'][key] == a['answer'][key]
        elif (b['status']=='limit' and a['status']=='ok'
              and b['median_seconds'] >= args.limit):
            row['speedup_lower_bound'] = args.limit/a['median_seconds']
        out['cases'].append(row)
        args.output.write_text(json.dumps(out, indent=2)+'\n')
    failures = [r['id'] for r in out['cases'] if r.get('agrees') is False or
                any(r[e]['status']=='error' for e in ('baseline','optimized'))]
    if failures:
        raise SystemExit('Benchmark errors/disagreements: '+', '.join(failures))

if __name__ == '__main__':
    main()
