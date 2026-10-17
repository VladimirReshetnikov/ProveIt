#!/usr/bin/env python3
"""Deterministically regenerate and check the supplied finite artifacts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True

def run(*args):
    result = subprocess.run([sys.executable, '-B', *args], cwd=HERE, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    print('PASS', ' '.join(args), flush=True)

def main():
    manifest = HERE / 'MANIFEST.sha256'
    pinned = {}
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        pinned[name] = expected
    # Reject changed source, checker or backend inputs before executing them.
    for name, expected in pinned.items():
        if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != expected:
            raise ValueError('Supplied artifact hash differs: ' + name)
    for nextproof, filename in ((0, 'register_abstract_np0.json'), (2, 'register_abstract_k3.json')):
        run('register_abstract.py', 'inputs/Prog254.v', '--cutoff', '3',
            '--nextproof', str(nextproof), '--output', filename)
        run('verify_register_certificate.py', 'inputs/Prog254.v', filename,
            '--output', 'register_check_np' + str(nextproof) + '.json')
    run('compile_global.py')
    run('zero_macro_search.py')
    run('verify_assembly.py')
    for name, expected in pinned.items():
        if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != expected:
            raise ValueError('Regenerated artifact bytes differ: ' + name)
    print(json.dumps({'passed': True, 'manifest_files_checked': len(pinned),
                      'byte_identical_reproduction': True}, indent=2))

if __name__ == '__main__':
    main()
