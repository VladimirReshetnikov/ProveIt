#!/usr/bin/env python3
"""Run stages 311–325 with sampled Lean-process and available-memory evidence."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
OUT = HERE / 'observations' / 'execution-monitor'
MIN_AVAILABLE_KIB = 8 * 1024 * 1024

def sample():
    available = None
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            available = int(line.split()[1])
            break
    if available is None:
        raise RuntimeError('cannot determine available memory')
    proc = subprocess.run(['ps', '-eo', 'pid=,ppid=,stat=,rss=,args='],
                          check=True, capture_output=True, text=True)
    children = []
    for line in proc.stdout.splitlines():
        parts = line.strip().split(None, 4)
        if len(parts) == 5 and '/bin/lean ' in parts[4]:
            children.append({'pid': int(parts[0]), 'ppid': int(parts[1]),
                             'state': parts[2], 'rss_kib': int(parts[3]), 'args': parts[4]})
    return {'utc': datetime.now(timezone.utc).isoformat(), 'mem_available_kib': available,
            'lean_processes': children}

def main():
    if OUT.exists():
        raise RuntimeError('refusing to overwrite execution evidence')
    initial = sample()
    if initial['mem_available_kib'] < MIN_AVAILABLE_KIB or len(initial['lean_processes']) >= 2:
        raise RuntimeError('insufficient available memory or both Lean slots already occupied')
    OUT.mkdir(parents=True)
    start = time.monotonic()
    samples = [initial]
    with (OUT / 'runner.stdout').open('w') as stdout, (OUT / 'runner.stderr').open('w') as stderr:
        proc = subprocess.Popen([sys.executable, '-I', '-B', str(HERE / 'run.py'), '15'],
                                stdout=stdout, stderr=stderr)
        print(json.dumps({'event': 'started', 'runner_pid': proc.pid,
                          'initial_mem_available_kib': initial['mem_available_kib']}), flush=True)
        while proc.poll() is None:
            time.sleep(5)
            row = sample()
            samples.append(row)
            if row['mem_available_kib'] < MIN_AVAILABLE_KIB or len(row['lean_processes']) > 2:
                print(json.dumps({'event': 'resource_threshold_observed', **row}), flush=True)
        code = proc.returncode
    result = {'runner_pid': proc.pid, 'exit_code': code,
              'duration_seconds': round(time.monotonic() - start, 3),
              'sample_interval_seconds': 5, 'minimum_available_kib': min(x['mem_available_kib'] for x in samples),
              'maximum_sampled_lean_processes': max(len(x['lean_processes']) for x in samples),
              'samples': samples,
              'scope': 'sampled evidence only; short overlaps can occur between samples'}
    (OUT / 'monitor.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ('exit_code', 'duration_seconds', 'minimum_available_kib',
                                            'maximum_sampled_lean_processes')}), flush=True)
    if code != 0:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
