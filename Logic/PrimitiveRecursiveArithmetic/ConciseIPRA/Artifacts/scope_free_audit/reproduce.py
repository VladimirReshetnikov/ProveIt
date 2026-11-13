"""Verify the delivered manifest, remeasure, and optionally run the suites."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tests', action='store_true')
    args = parser.parse_args()
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.exists():
        raise SystemExit('Missing MANIFEST.sha256')
    checked = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit('Manifest mismatch: ' + relative)
        checked += 1
    print('Manifest verified:', checked, 'files', flush=True)
    subprocess.run([sys.executable, str(ROOT / 'measure.py')], cwd=ROOT, check=True)
    if args.tests:
        subprocess.run([sys.executable, str(ROOT / 'tests/verify_sorted.py')],
                       cwd=ROOT, check=True)
        subprocess.run([sys.executable, str(ROOT / 'scope_free/verify.py')],
                       cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
