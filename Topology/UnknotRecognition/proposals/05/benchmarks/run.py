"""Reproduce paired cold-process measurements; never convert a timeout to a verdict.

Run from any directory: python benchmarks/run.py --repeats 3 --seconds 3
Input construction, interpreter startup, and the first input parse are excluded.
Each timed function call starts with fresh caches in its own subprocess.
"""
from __future__ import annotations

import argparse
import csv
import datetime
import json
import os
import platform
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT)]
from fastunknot import Diagram


def cases():
    jobs = []
    original = ['unknot', 'trefoil', 'figure_eight', 'hard_unknot_8',
                'kinoshita_terasaka', 'conway', 'torus_3_5', 'unknot_braid40',
                'grid_determinant_one_knot', 'grid_scrambled_unknot']
    for name in original + ['conway_sum_2', 'conway_sum_3', 'conway_sum_4']:
        data = json.loads((ROOT / 'examples' / (name + '.json')).read_text())
        jobs.append(dict(name=name, kind='recognize', input=data))
    for name in ['conway', 'kinoshita_terasaka', 'hard_unknot_8', 'torus_3_5']:
        data = json.loads((ROOT / 'examples' / (name + '.json')).read_text())
        jobs.append(dict(name='raw_' + name, kind='rank', input=data))
    for n in (256, 1024):
        data = {'braid': {'strands': n + 1, 'word': list(range(1, n + 1))}}
        data = {'pd': [list(x) for x in Diagram.from_json(data).pd]}
        jobs.append(dict(name='raw_unknot_chain_' + str(n), kind='rank', input=data))
        jobs.append(dict(name='ordering_chain_' + str(n), kind='ordering', input=data))
    data = {'braid': {'strands': 5, 'word':
        [-4,-3,4,4,-3,2,1,1,-1,-1,3,-4,-1,3,2,2,-2,-1,-3,2,3,-3,-4,-4,
         -3,3,1,3,-2,-4,-4,3,-3,3,-4,-2]}}
    jobs.append(dict(name='raw_random5_36', kind='rank', input=data))
    data = json.loads((ROOT / 'examples' / 'hard_unknot_8.json').read_text())
    jobs.append(dict(name='forced_hard_unknot_8', kind='recognize', input=data,
                     options={'use_reduction': False, 'use_descending': False}))
    for job in jobs:
        job['crossings'] = Diagram.from_json(job['input']).crossings
    return jobs


def cpu_description():
    try:
        for line in Path('/proc/cpuinfo').read_text().splitlines():
            if line.startswith('model name'):
                return line.split(':', 1)[1].strip()
    except OSError:
        pass
    return platform.processor()


def aggregate(trials):
    keys = dict.fromkeys((x['name'], x['kind'], x['engine']) for x in trials)
    rows = []
    for name, kind, engine in keys:
        group = [x for x in trials if (x['name'], x['kind'], x['engine']) ==
                 (name, kind, engine)]
        completed = [x for x in group if x['outcome'] == 'completed']
        timed = [x['elapsed'] for x in group if x.get('elapsed') is not None]
        success_times = [x['elapsed'] for x in completed]
        methods = sorted(set(x.get('result', {}).get('method', '') for x in completed))
        ranks = sorted(set(x['result']['reduced_rank'] for x in completed
                           if 'reduced_rank' in x.get('result', {})))
        rows.append(dict(name=name, kind=kind, engine=engine,
            crossings=group[0]['crossings'], trials=len(group), completed=len(completed),
            outcome=','.join(sorted(set(x['outcome'] for x in group))),
            median_completed_seconds=statistics.median(success_times) if success_times else None,
            minimum_completed_seconds=min(success_times) if success_times else None,
            maximum_completed_seconds=max(success_times) if success_times else None,
            median_observed_seconds=statistics.median(timed) if timed else None,
            methods=','.join(methods), reduced_ranks=','.join(map(str, ranks))))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--seconds', type=float, default=3.0)
    parser.add_argument('--name', help='Run only cases containing this substring')
    parser.add_argument('--output', type=Path, default=ROOT / 'results' / 'benchmark.json')
    args = parser.parse_args()
    if args.repeats < 1 or args.seconds <= 0:
        parser.error('repeats and seconds must be positive')
    suite = [x for x in cases() if not args.name or args.name in x['name']]
    env = os.environ.copy()
    env['PYTHONHASHSEED'] = '0'
    record = {'environment': {'python': sys.version, 'platform': platform.platform(),
        'machine': platform.machine(), 'cpu': cpu_description(),
        'logical_cpus': os.cpu_count(), 'hash_seed': '0',
        'timestamp_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'clock': 'time.perf_counter', 'worker_python_flags': ['-S'], 'caches': 'fresh process for every timed call',
        'excluded': 'interpreter/import startup and initial Diagram.from_json',
        'soft_seconds': args.seconds, 'hard_seconds': args.seconds + 2.5,
        'repeats': args.repeats}, 'cases': suite, 'trials': []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for case_index, case in enumerate(suite):
        for repeat in range(args.repeats):
            engines = ('baseline', 'optimized') if (case_index + repeat) % 2 == 0 else (
                       'optimized', 'baseline')
            for engine in engines:
                job = {**case, 'engine': engine, 'seconds': args.seconds}
                began = time.perf_counter()
                trial = {k: v for k, v in job.items() if k not in ('input', 'options')}
                trial['repeat'] = repeat + 1
                try:
                    proc = subprocess.run([sys.executable, '-S', str(ROOT / 'benchmarks' / 'worker.py')],
                        input=json.dumps(job), text=True, capture_output=True, env=env,
                        timeout=args.seconds + 2.5, cwd=ROOT)
                    trial['returncode'] = proc.returncode
                    if proc.returncode:
                        trial.update(outcome='error', stderr=proc.stderr[-10000:])
                    else:
                        payload = json.loads(proc.stdout)
                        trial.update(payload)
                        status = payload.get('result', {}).get('status')
                        trial['outcome'] = ('resource-limit' if status == 'UNKNOWN' or
                            payload.get('limit') else 'completed')
                except subprocess.TimeoutExpired:
                    trial.update(outcome='hard-timeout', elapsed=None)
                trial['process_wall_seconds'] = time.perf_counter() - began
                record['trials'].append(trial)
                record['summary'] = aggregate(record['trials'])
                args.output.write_text(json.dumps(record, indent=2) + '\n')
                print(f"{case['name']:29s} {engine:9s} {repeat+1}: "
                      f"{trial['outcome']:14s} {trial.get('elapsed', 'n/a')}", flush=True)
    csv_path = args.output.with_suffix('.csv')
    with csv_path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(record['summary'][0]))
        writer.writeheader()
        writer.writerows(record['summary'])

if __name__ == '__main__':
    main()
