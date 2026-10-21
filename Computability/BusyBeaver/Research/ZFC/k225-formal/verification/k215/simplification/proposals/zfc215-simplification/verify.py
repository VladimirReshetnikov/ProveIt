#!/usr/bin/env python3
"""Finite reproduction checks; proof builds remain explicit separate targets."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

if not __debug__:
    raise RuntimeError('Run with assertions enabled.')
ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    manifest = json.loads((ROOT / 'manifest.json').read_text())
    for name, digest in manifest['files'].items():
        assert sha(ROOT / name) == digest, 'Manifest mismatch: ' + name
    checks = []
    def run(name, command):
        start = time.monotonic()
        p = subprocess.run([sys.executable, '-B', *map(str, command)], cwd=ROOT,
                           text=True, capture_output=True)
        if p.returncode:
            raise RuntimeError(name + '\n' + p.stdout + p.stderr)
        checks.append({'check': name, 'exit_code': p.returncode,
                       'seconds': time.monotonic() - start,
                       'output': p.stdout.strip()})
        print(name + ': PASS', flush=True)
    with tempfile.TemporaryDirectory(prefix='zfc215-finite-') as temp:
        temp = Path(temp)
        run('Literal M124/Rocq inputs', [ROOT/'m124_rocq/check_inputs.py'])
        run('Literal Lean data', [ROOT/'m124_lean/generate_data.py',
              ROOT/'m124_rocq/k215.native.tm', '--output',
              ROOT/'m124_lean/Marker124Data.lean', '--check'])
        run('All calibrated prefix boundaries', [ROOT/'checks/replay_marker.py',
              ROOT/'m124_rocq/k215.native.tm',ROOT/'m124_rocq/machine.native.tm',
              '--output',temp/'boot.json'])
        assert json.loads((temp/'boot.json').read_text()) == json.loads(
            (ROOT/'checks/m124_boot_replay.json').read_text())
        run('Complete read-input quotient obstruction', [ROOT/'checks/quotient_obstruction.py',
              ROOT/'m124_rocq/machine.native.tm',temp/'quotient'])
        for file in ['summary.json','witnesses.json.gz']:
            assert (temp/'quotient'/file).read_bytes() == (ROOT/'checks/quotient_m124'/file).read_bytes()
        run('Independent unbounded source invariant', [ROOT/'research214/code/check_invariant.py',
              ROOT/'research214/inputs/sites215.json',ROOT/'research214/results/abstract_source_k2.json'])
        run('Saved reassociation evidence', [ROOT/'research214/code/check_saved_rotations.py'])
    result = {'status':'PASS_FINITE_CHECKS', 'snapshot':manifest['snapshot'],
              'manifest_files_verified':len(manifest['files']), 'checks':checks,
              'scope':'Finite reproduction only. Kernel builds and timed searches have separate records.'}
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))

if __name__ == '__main__':
    main()
