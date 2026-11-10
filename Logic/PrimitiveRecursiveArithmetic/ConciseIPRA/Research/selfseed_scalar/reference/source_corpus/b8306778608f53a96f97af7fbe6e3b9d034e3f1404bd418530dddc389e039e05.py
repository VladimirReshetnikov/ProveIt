"""Offline reproduction: integrity, whole-source measurements and concrete checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.is_file():
        raise FileNotFoundError('MANIFEST.sha256 is required for distributed reproduction')
    checked = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('Payload integrity mismatch: ' + relative)
        checked += 1
    print('Payload hashes verified:', checked, flush=True)


def main():
    verify_manifest()
    scripts = ('measure.py', 'tests/verify_saved.py', 'tests/alias_controls.py',
               'tests/mutation_controls.py', 'tests/check_readable.py',
               'tests/independent_audit.py')
    receipts = []
    for script in scripts:
        p = subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT,
                           text=True, capture_output=True)
        receipts.append(dict(script=script, returncode=p.returncode,
                             stdout=p.stdout, stderr=p.stderr))
        print(script + ': ' + ('PASS' if p.returncode == 0 else 'FAIL'), flush=True)
        if p.returncode:
            print(p.stdout)
            print(p.stderr)
            raise SystemExit(p.returncode)
    print('All offline checks passed. Finite tests do not certify the metatheorems.')


if __name__ == '__main__':
    main()
