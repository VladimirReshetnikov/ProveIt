#!/usr/bin/env python3
"""Verify package integrity, the two test suites, and saved exact certificates.

The stored benchmark/test records are left untouched.  Regenerating figures
or rebuilding the PDF can legitimately change their release checksums.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def check_hashes():
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.exists():
        print('Release checksum manifest has not yet been generated.', flush=True)
        return
    checked = 0
    for line in manifest.read_text().splitlines():
        if not line.strip():
            continue
        digest, relative = line.split('  ', 1)
        target = (ROOT / relative).resolve()
        if not target.is_relative_to(ROOT):
            raise ValueError('Manifest path escapes the package')
        if hashlib.sha256(target.read_bytes()).hexdigest() != digest:
            raise ValueError('Checksum mismatch: ' + relative)
        checked += 1
    print(f'Verified {checked} release file checksums.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hashes-only', action='store_true')
    parser.add_argument('--skip-hashes', action='store_true',
                        help='use after intentionally editing or rebuilding the package')
    args = parser.parse_args()
    if not args.skip_hashes:
        check_hashes()
    if args.hashes_only:
        return
    calls = [
        (ROOT / 'fast', [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v']),
        (ROOT, [sys.executable, '-m', 'unittest', 'hierarchy.test_ball_patterns', '-v']),
        (ROOT, [sys.executable, 'experiments/export_certificates.py', '--verify-existing']),
    ]
    for cwd, command in calls:
        subprocess.run(command, cwd=cwd, check=True)
    print('All scanner tests, terminal tests, and saved exact certificates passed.')


if __name__ == '__main__':
    main()
