#!/usr/bin/env python3
"""Offline exact reconstruction and verification in a disposable directory."""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def manifest():
    count = 0
    for row in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, rel = row.split('  ', 1)
        path = ROOT / rel
        need(path.is_file(), 'Missing release file: ' + rel)
        need(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
             'Release hash mismatch: ' + rel)
        count += 1
    return count


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick', action='store_true', help='Explicitly skip universal runtime replay')
    p.add_argument('--parent-replay', action='store_true', help='Also replay the retained full Joint release')
    p.add_argument('--output', type=Path, help='Write the final receipt outside the sealed package')
    a = p.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Use Python without -O for the full orchestrator')
    began = time.monotonic()
    checked = manifest()
    receipts = {}
    with tempfile.TemporaryDirectory(prefix='u208-verify-') as temp:
        temp = Path(temp)
        machines = temp / 'machine'
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
        def run(script, arguments, optimized=False):
            command = [sys.executable, '-B'] + (['-O'] if optimized else [])
            command += [str(ROOT / script)] + [str(x) for x in arguments]
            result = subprocess.run(command, env=environment, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise RuntimeError('Verification failed: ' + script)
            print(script + (' (-O)' if optimized else '') + ': PASS', flush=True)
        run('code/build.py', ['--output', machines])
        for name in ('u208.native.tm', 'u208.tm', 'state_map.json', 'sites.json',
                     'u208_compatibility.native.tm', 'u208_compatibility.tm'):
            need((machines / name).read_bytes() == (ROOT / 'machine' / name).read_bytes(),
                 'Reconstruction differs: ' + name)
        run('code/verify_fold.py', ['--old', ROOT / 'baseline/u209.native.tm',
            '--new', machines / 'u208.native.tm', '--output', temp / 'local.json'])
        run('code/verify_fold.py', ['--old', ROOT / 'baseline/u209.native.tm',
            '--new', machines / 'u208.native.tm', '--output', temp / 'local_optimized.json'], True)
        run('code/check_alternative.py', ['--machine', machines, '--output', temp / 'alternative.json'])
        run('code/compare_snapshots.py', ['--root', ROOT, '--output', temp / 'comparison.json'])
        run('code/check_source_startup.py', ['--machine', machines, '--output', temp / 'startup.json'])
        for key, file in [('local', 'local.json'), ('local_optimized', 'local_optimized.json'),
                          ('alternative', 'alternative.json'), ('comparison', 'comparison.json'),
                          ('source_startup', 'startup.json')]:
            receipts[key] = json.loads((temp / file).read_text())
        if a.quick:
            receipts['runtime'] = {'status': 'EXPLICITLY_SKIPPED_BY_QUICK_OPTION'}
        else:
            print('Replaying all 5,084 arbitrary-natural contracts; this takes a few minutes.', flush=True)
            run('code/check_runtime.py', ['--machine', machines, '--output', temp / 'runtime'])
            receipts['runtime'] = json.loads((temp / 'runtime/runtime.json').read_text())
        if a.parent_replay:
            with zipfile.ZipFile(ROOT / 'baseline/U209_ConPA_Joint_2026-10-29.zip') as z:
                z.extractall(temp / 'parent')
            parent = temp / 'parent/U209_ConPA_Joint_2026-10-29/reproduce.py'
            result = subprocess.run([sys.executable, '-B', str(parent)], cwd=parent.parent,
                                    env=environment, capture_output=True, text=True)
            need(result.returncode == 0, 'Retained full-parent replay failed: ' + result.stdout)
            receipts['parent_replay'] = {'status': 'FULL_PARENT_RELEASE_PASS'}
    result = {'status': 'U208_QUICK_PASS' if a.quick else 'U208_FULL_REPLAY_PASS',
              'manifest_files': checked, 'seconds': time.monotonic() - began,
              'working_states': 208, 'transition_rows': 416, 'checks': receipts,
              'scope': 'Ordinary mathematical certificates; no exported formal PA endpoint.'}
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
