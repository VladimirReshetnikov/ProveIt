#!/usr/bin/env python3
"""Compile the small standard-library-only Coq proof and run recursive coqchk.
Use the desired toolchain's environment; no dependency download is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

MODULES = ['EarlyHaltSelection', 'NativeSelection']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--coqc', default='coqc')
    p.add_argument('--coqchk', default='coqchk')
    a = p.parse_args()
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    src = Path(__file__).resolve().parent
    for m in MODULES:
        shutil.copy2(src / (m + '.v'), out / (m + '.v'))
    records = []
    cmds = [[a.coqc, '--version']] + [[a.coqc, '-q', m + '.v'] for m in MODULES] + [
        [a.coqchk, '-silent'] + MODULES]
    for i, cmd in enumerate(cmds):
        start = time.monotonic()
        r = subprocess.run(cmd, cwd=out, capture_output=True, text=True, timeout=120)
        log = f'{i:02d}.log'
        (out / log).write_text(r.stdout + r.stderr)
        records.append({'command': cmd, 'returncode': r.returncode,
                        'seconds': time.monotonic() - start, 'log': log,
                        'log_sha256': digest(out / log)})
        if r.returncode:
            break
    receipt = {
        'status': 'PASS_COMPILED_AND_KERNEL_RECHECKED' if len(records) == 4 and all(
            r['returncode'] == 0 for r in records) else 'FAIL',
        'source_hashes': {m + '.v': digest(src / (m + '.v')) for m in MODULES},
        'object_hashes': {m + '.vo': digest(out / (m + '.vo')) for m in MODULES
                          if (out / (m + '.vo')).exists()},
        'actions': records,
        'scope': 'Generic selector and numeric command-shape adapter only; no K215 endpoint rebuild.'
    }
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    raise SystemExit(0 if receipt['status'].startswith('PASS') else 1)


if __name__ == '__main__':
    main()
