#!/usr/bin/env python3
"""Compile the small production EnumPerm closure and the concrete adapter.

Only .lean source inputs are copied. The build does not use old project .olean
files. Every proof process takes the shared proof-compiler lock.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path('/workspace/scratch/c995d38c8a66/ProveIt')
HERE = Path(__file__).resolve().parent
OUT = HERE / 'concrete'
LEAN = Path('/workspace/scratch/c995d38c8a66/toolchains/lean-4.32.0-linux/bin/lean')
LOCK = '/workspace/scratch/c995d38c8a66/work/proof-compiler.lock'
PREFIXES = {'BusyBeaver': ROOT / 'Computability/BusyBeaver/Lean',
            'FirstOrder': ROOT / 'Logic/FirstOrder/Lean'}

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def imports(p):
    return [n for line in p.read_text().splitlines() if line.startswith('import ')
            for n in line[7:].split()]

seen, plan = set(), []

def visit(n):
    if n in seen or n.split('.')[0] not in PREFIXES:
        return
    seen.add(n)
    rel = Path(n.replace('.', '/') + '.lean')
    src = PREFIXES[n.split('.')[0]] / rel
    for dep in imports(src):
        visit(dep)
    plan.append((n, src, rel))

visit('BusyBeaver.ZFC.EnumPerm')
OUT.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(OUT) + ':' + str(HERE))
records = []
receipt = {'commit': 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6',
           'status': 'RUNNING', 'records': records, 'compiler': str(LEAN),
           'compiler_sha256': digest(LEAN),
           'kernel_inputs': {n: digest(HERE / (n + '.lean'))
                             for n in ['CofinalScheduler', 'BoundedScheduler']}}

def save():
    (HERE / 'concrete_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')

version = subprocess.run(['flock', LOCK, str(LEAN), '--version'],
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
receipt['version'] = version.stdout.strip()
save()

for name, src, rel in plan + [('K215BoundedScheduler', HERE / 'K215BoundedScheduler.lean',
                               Path('K215BoundedScheduler.lean'))]:
    dst = OUT / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    cmd = ['flock', LOCK, str(LEAN), '-o', str(rel.with_suffix('.olean')), str(rel)]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=OUT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    duration = time.monotonic() - start
    log = OUT / rel.with_suffix('.log')
    log.write_text(result.stdout)
    record = dict(module=name, source=str(src), copied_source=str(dst),
                  source_sha256=digest(src), command=cmd, cwd=str(OUT),
                  lean_path=env['LEAN_PATH'], exit_code=result.returncode,
                  stdout_stderr=str(log.relative_to(HERE)),
                  log_sha256=digest(log), elapsed_seconds=duration)
    if result.returncode == 0:
        record['object_sha256'] = digest(dst.with_suffix('.olean'))
    records.append(record)
    print(name, 'PASS' if result.returncode == 0 else 'FAIL', f'{duration:.3f}s', flush=True)
    save()
    if result.returncode:
        print(result.stdout, flush=True)
        receipt['status'] = 'FAIL'
        save()
        raise SystemExit(result.returncode)

receipt['status'] = 'PASS'
save()
