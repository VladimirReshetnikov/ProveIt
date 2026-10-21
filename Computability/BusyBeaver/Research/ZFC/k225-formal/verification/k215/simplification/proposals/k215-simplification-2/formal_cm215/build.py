#!/usr/bin/env python3
"""Serial Lean 4.32 build with retained per-module logs and source hashes.
No network, proof search, native_decide, or mathlib dependency is required.
The full pre-existing ZFC endpoint is intentionally not rebuilt here.
"""
import argparse, hashlib, json, os, subprocess, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--lean', default='lean')
p.add_argument('--out', type=Path, default=HERE / '_build')
a = p.parse_args()
out = a.out.resolve()
out.mkdir(parents=True, exist_ok=True)
modules = [
    (HERE, 'PositiveSimulation'), (HERE, 'MarkerTransfer'), (HERE, 'CM215Exact'),
    (HERE/'vendor', 'BusyBeaver/Core'), (HERE/'vendor', 'BusyBeaver/ZFC/KZip'),
    (HERE/'vendor', 'BusyBeaver/ZFC/KTableCore'), (HERE/'vendor', 'BusyBeaver/ZFC/KTable215'),
    (HERE/'vendor', 'BusyBeaver/ZFC/KDenseBridge'), (HERE/'vendor', 'BusyBeaver/ZFC/KDense215'),
    (HERE, 'CoreNativeBridge'), (HERE, 'CM215Core')]
version = subprocess.check_output([a.lean, '--version'], text=True).strip()
records = []
env = os.environ.copy()
env['LEAN_PATH'] = str(out)
for root, name in modules:
    source = root / (name + '.lean')
    dest = out / (name + '.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    log = out / (name.replace('/', '.') + '.log')
    begin = time.monotonic()
    proc = subprocess.run([a.lean, '-o', str(dest), str(Path(name + '.lean'))],
                          cwd=root, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
    log.write_text(proc.stdout)
    record = {'module': name.replace('/', '.'), 'source': str(source.relative_to(HERE)),
              'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'seconds': time.monotonic()-begin, 'exit_code': proc.returncode,
              'log': str(log.relative_to(out)), 'sorryAx': 'sorryAx' in proc.stdout,
              'warnings': proc.stdout.count('warning:')}
    records.append(record)
    print(json.dumps(record), flush=True)
    (out/'build.json').write_text(json.dumps({'lean_version':version, 'records':records},indent=2)+'\n')
    if proc.returncode != 0 or record['sorryAx']:
        raise SystemExit('Build failed: '+str(log))
print('ALL_11_MODULES_PASS')
