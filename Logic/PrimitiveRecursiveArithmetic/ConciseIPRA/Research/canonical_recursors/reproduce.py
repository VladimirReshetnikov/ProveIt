#!/usr/bin/env python3
"""Verify the frozen archive and reproduce its executable evidence."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.exists():
        print('No frozen manifest present; continuing with reproduction.')
        return
    checked = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f'Manifest mismatch: {relative}')
        checked += 1
    print(f'Verified {checked} frozen file hashes.', flush=True)


def run(directory, *arguments):
    subprocess.run([sys.executable, *arguments], cwd=ROOT / directory, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='also rebuild report.tex and report.pdf')
    parser.add_argument('--skip-manifest', action='store_true', help='use after intentionally regenerating files')
    args = parser.parse_args()
    if not args.skip_manifest:
        verify_manifest()
    print('Reference measurements use CPython 3.12.14; running', sys.version.split()[0], flush=True)
    run('strict', 'build_family.py')
    run('strict', 'test_family.py')
    run('compact', 'reproduce.py')
    if args.pdf:
        run('.', 'assemble_report.py', '--compile')
    print('Reproduction completed successfully.', flush=True)


if __name__ == '__main__':
    main()
