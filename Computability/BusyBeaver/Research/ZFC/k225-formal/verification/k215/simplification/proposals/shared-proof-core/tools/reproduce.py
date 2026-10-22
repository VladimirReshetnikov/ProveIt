#!/usr/bin/env python3
"""Run focused kernel checks in a new output tree, without modifying the packet or repo."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    repo, lean, out = args.repo.resolve(), args.lean.resolve(), args.out.resolve()
    if out.exists():
        raise SystemExit('Use a new --out directory.')
    for tool in ['coqc', 'coqchk']:
        if not shutil.which(tool):
            raise SystemExit(tool + ' is required on PATH.')
    out.mkdir(parents=True)
    logs = out / 'logs'
    logs.mkdir()
    records = []
    lockpath = Path(tempfile.gettempdir()) / 'proveit-k215-proof-build.lock'

    def run(name, command, *, locked=False, env=None):
        print('Checking ' + name, flush=True)
        start = time.monotonic()
        with (logs / (name + '.log')).open('w') as log, lockpath.open('a') as lock:
            if locked:
                fcntl.flock(lock, fcntl.LOCK_EX)
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, env=env)
        record = {'name': name, 'command': [str(x) for x in command],
                  'returncode': result.returncode, 'seconds': time.monotonic() - start,
                  'log': 'logs/' + name + '.log'}
        records.append(record)
        (out / 'reproduction.json').write_text(json.dumps({
            'status': 'IN_PROGRESS' if result.returncode == 0 else 'FAIL',
            'scope': 'Focused logic, semantic simulation, Rocq adapter and progress example; no full K215 endpoint build.',
            'records': records}, indent=2) + '\n')
        if result.returncode:
            print((logs / (name + '.log')).read_text())
            raise SystemExit(result.returncode)

    # The component drivers may regenerate sources or receipts. Use copies.
    lean_inputs = out / 'lean_inputs'
    rocq_inputs = out / 'rocq_inputs'
    semantic_inputs = out / 'semantic_inputs'
    shutil.copytree(ROOT / 'lean_shared', lean_inputs)
    shutil.copytree(ROOT / 'rocq_core', rocq_inputs)
    shutil.copytree(ROOT / 'semantic_sites', semantic_inputs)
    run('lean_source_comparison', [sys.executable, str(lean_inputs / 'inspect_refactoring.py'), '--repo', str(repo)])
    run('lean_logic', [sys.executable, str(lean_inputs / 'verify_closure.py'),
                      '--repo', str(repo), '--lean', str(lean)], locked=True)
    run('semantic_source_comparison', [sys.executable, str(semantic_inputs / 'verify_invariants.py')])
    # This driver obtains the same compiler lock itself.
    run('lean_semantic', [sys.executable, str(semantic_inputs / 'build_semantic.py'),
                         '--lean', str(lean), '--out', str(out / 'semantic_build')])
    run('rocq_baseline_and_candidate', [sys.executable, str(rocq_inputs / 'reproduce.py'),
                                      '--out', str(out / 'rocq_build')], locked=True)
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    run('positive_progress_example', [str(lean), str(ROOT / 'explanatory/ProgressBoundary.lean')], locked=True, env=env)
    summary = {'status': 'PASS', 'scope': 'Focused component checks, not the full K215 endpoint.', 'records': records}
    (out / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
