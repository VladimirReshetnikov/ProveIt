#!/usr/bin/env python3
"""Bounded new author check; each attempt is immutable and directly guarded."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

if sys.flags.optimize:
    raise SystemExit('Optimized Python is not accepted')
parser = argparse.ArgumentParser()
parser.add_argument('--attempt', required=True, help='new lowercase attempt name')
args = parser.parse_args()
if not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', args.attempt):
    raise SystemExit('Attempt must be lowercase alphanumeric words separated by hyphens')

here = Path(__file__).resolve().parent
repo = here.parents[3]
source = here / 'SeedLines.lean'
project = Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
package = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
direct = project / 'DiophantineConsistency/DecimalMachine215.olean'
output_parent = Path('/tmp/current14-seed-lines-20261103/attempts')
receipt_parent = here / 'observations'
out = output_parent / args.attempt
receipt_dir = receipt_parent / args.attempt


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot():
    ps = subprocess.run(['ps', '-eo', 'pid=,comm=,rss=,args='],
                        capture_output=True, text=True, check=True).stdout
    leans = []
    for line in ps.splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) == 4 and fields[1] == 'lean':
            leans.append({'pid': int(fields[0]), 'rss_kib': int(fields[2]), 'args': fields[3]})
    for row in Path('/proc/meminfo').read_text().splitlines():
        if row.startswith('MemAvailable:'):
            available = int(row.split()[1])
            break
    else:
        raise RuntimeError('MemAvailable missing')
    return {'time_ns': time.time_ns(), 'available_kib': available, 'lean_processes': leans}


for file in (source, direct, lean, here / 'run.py', here / 'run-captured.txt'):
    if not file.is_file():
        raise SystemExit(f'Missing required input: {file}')
if not package.is_dir():
    raise SystemExit(f'Missing package provider: {package}')
if out.exists() or receipt_dir.exists():
    raise SystemExit('Attempt already exists; choose a fresh name')
pre = snapshot()
if pre['available_kib'] < 8 * 1024 * 1024 or len(pre['lean_processes']) >= 2:
    raise SystemExit('Resource guard refused launch')
output_parent.mkdir(parents=True, exist_ok=True)
receipt_parent.mkdir(parents=True, exist_ok=True)
# mkdir is atomic and refuses a competing or existing attempt; no removal on failure.
out.mkdir()
receipt_dir.mkdir()
inputs = [source, direct, lean, here / 'run.py', here / 'run-captured.txt']
before = {str(p): {'sha256': digest(p), 'realpath': str(p.resolve())} for p in inputs}
env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{project}:{package}', 'LEAN_NUM_THREADS': '1'}
cmd = [str(lean), '-M', '2000', '-o', str(out / 'SeedLines.olean'), str(source)]
samples = []
start = time.monotonic()
reason = None
with (out / 'stdout.log').open('x') as stdout_file, (out / 'stderr.log').open('x') as stderr_file:
    proc = subprocess.Popen(cmd, stdout=stdout_file, stderr=stderr_file,
                            env=env, cwd=repo, text=True)
    while proc.poll() is None:
        snap = snapshot()
        samples.append(snap)
        if snap['available_kib'] < 8 * 1024 * 1024 or len(snap['lean_processes']) > 2:
            reason = 'resource guard'
            proc.kill()
            break
        if time.monotonic() - start > 180:
            reason = 'timeout'
            proc.kill()
            break
        time.sleep(2)
    proc.wait()
stdout = (out / 'stdout.log').read_text()
stderr = (out / 'stderr.log').read_text()
after = {str(p): {'sha256': digest(p), 'realpath': str(p.resolve())} for p in inputs}
log = stdout + stderr
object_path = out / 'SeedLines.olean'
marker = "'DiophantineConsistency.Current14SeedLines.decimal_lines_eq_seed' does not depend on any axioms"
result = {'attempt': args.attempt, 'command': cmd, 'lean_path': env['LEAN_PATH'],
          'before': before, 'after': after, 'preflight': pre, 'samples': samples,
          'elapsed_seconds': time.monotonic()-start, 'exit': proc.returncode, 'reason': reason,
          'stdout': stdout, 'stderr': stderr,
          'object_sha256': digest(object_path) if object_path.is_file() else None}
with (receipt_dir / 'observation.json').open('x') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
passed = (proc.returncode == 0 and reason is None and before == after and
          object_path.is_file() and marker in stdout and not stderr and
          not any(token in log for token in ('error:', 'warning:', 'sorryAx')))
print(json.dumps({'attempt': args.attempt, 'passed': passed, 'exit': proc.returncode,
                  'reason': reason, 'unchanged': before == after,
                  'stdout': stdout, 'stderr': stderr,
                  'elapsed_seconds': result['elapsed_seconds']}))
if not passed:
    sys.exit(1)
