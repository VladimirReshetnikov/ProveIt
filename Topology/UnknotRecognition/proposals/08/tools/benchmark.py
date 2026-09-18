"""Serial, process-isolated cold comparisons against the preserved input baseline.

Each invocation imports one implementation, validates the same PD, then starts
its timer. The parent enforces a hard subprocess timeout. Results contain all
trials, generated inputs, environment information and honest censoring flags.
"""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
from time import perf_counter
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram
from fastunknot.decompose import connected_sum


def load(name):
    return Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))


def power(d, k):
    result = Diagram.from_pd([])
    for _ in range(k):
        result = connected_sum(result, d)
    return result


def invoke(request, timeout):
    start = perf_counter()
    try:
        proc = subprocess.run([sys.executable, str(ROOT/'tools/worker.py')],
                              input=json.dumps(request), capture_output=True, text=True,
                              env={**os.environ, 'PYTHONHASHSEED': '0'}, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'completed': False, 'reason': 'external subprocess timeout',
                'external_wall_seconds': perf_counter()-start, 'timeout_seconds': timeout}
    if proc.returncode:
        return {'completed': False, 'reason': 'worker error', 'returncode': proc.returncode,
                'stderr': proc.stderr, 'stdout': proc.stdout}
    result = json.loads(proc.stdout)
    result['external_wall_seconds'] = perf_counter()-start
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trials', type=int, default=3)
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--hard-timeout', type=float, default=30)
    parser.add_argument('--output', type=Path, default=ROOT/'results/benchmarks.json')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--max-cases', type=int, default=None)
    args = parser.parse_args()
    if args.trials < 1 or args.timeout <= 0 or args.hard_timeout <= 0:
        parser.error('trials and timeouts must be positive')
    jobs = []
    def add(name, d, mode, repetitions=None, timeout=None):
        jobs.append({'name': name, 'diagram': d.to_json(), 'crossings': d.crossings,
                     'mode': mode, 'repetitions': repetitions or args.trials,
                     'timeout': timeout or args.timeout})
    for name in ('trefoil', 'hard_unknot_8', 'conway', 'kinoshita_terasaka',
                 'torus_3_5', 'unknot_braid40', 'baseline_timeout36'):
        add(name, load(name), 'pipeline')
    for name in ('hard_unknot_8', 'conway', 'kinoshita_terasaka',
                 'torus_3_5', 'unknot_braid40'):
        add(name, load(name), 'scan')
    add('baseline_timeout36', load('baseline_timeout36'), 'scan', 1, args.hard_timeout)
    for k in (2, 3, 6, 12):
        add(f'conway_sum_{k}', power(load('conway'), k), 'rank',
            repetitions=3 if k==2 else 1, timeout=5)
    add('trefoil_sum_10', power(load('trefoil'), 10), 'rank', 1, 5)
    for n in (256, 1024):
        add(f'unknot_chain_{n}', Diagram.from_braid(n+1, list(range(1,n+1))), 'order')
    add('torus_2_501', Diagram.from_braid(2, [1]*501), 'descending')
    output = {'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'environment': {'python': sys.version, 'platform': platform.platform(),
                              'machine': platform.machine(), 'cpu_count': os.cpu_count(),
                              'pythonhashseed': '0'},
              'protocol': {'cold_process_each_trial': True, 'serial': True,
                           'input_validation_excluded': True, 'timing_unit': 'seconds',
                           'timeout_includes_imports': True}, 'cases': []}
    try:
        output['environment']['cpu_model'] = next(
            line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
            if line.startswith('model name'))
    except (OSError, StopIteration):
        pass
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.resume and args.output.exists():
        output = json.loads(args.output.read_text())
    finished = {(c['name'], c['mode']) for c in output['cases']}
    processed = 0
    for job in jobs:
        if (job['name'], job['mode']) in finished:
            continue
        if args.max_cases is not None and processed >= args.max_cases:
            break
        processed += 1
        case = dict(job)
        for implementation in ('baseline','accelerated'):
            trials = []
            for i in range(job['repetitions']):
                request = {'implementation': implementation, 'mode': job['mode'],
                           'diagram': job['diagram']}
                # Cooperative limit starts after imports; the external process
                # cap also covers expensive code with infrequent checks.
                if job['mode'] in ('scan','rank'):
                    request['seconds'] = max(0.1, job['timeout']-0.5)
                trial = invoke(request, job['timeout'])
                trials.append(trial)
                if not trial['completed']:
                    break
            complete = [r['seconds'] for r in trials if r['completed']]
            case[implementation] = {'trials': trials,
                'all_completed': len(complete)==job['repetitions'],
                'median_seconds': statistics.median(complete) if len(complete)==job['repetitions'] else None}
        output['cases'].append(case)
        args.output.write_text(json.dumps(output, indent=2)+'\n')
        print(f"{case['mode']:10s} {case['name']:24s} "
              f"baseline={case['baseline']['median_seconds']} "
              f"accelerated={case['accelerated']['median_seconds']}", flush=True)
    return output

if __name__ == '__main__':
    main()
