"""Verify delivery integrity, remeasure, and optionally run targeted checks."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--tests', action='store_true')
args = parser.parse_args()
manifest = ROOT/'MANIFEST.sha256'
if manifest.exists():
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != digest:
            raise SystemExit('Integrity mismatch: '+name)
    print('Manifest verified.', flush=True)
subprocess.run([sys.executable, str(ROOT/'measure.py')], check=True)
if args.tests:
    for name in ('verify.py', 'verify_readable.py', 'audit_retained.py', 'focused_validation.py', 'verify_profiles.py'):
        path = ROOT/'tests'/name
        if path.exists():
            subprocess.run([sys.executable, str(path)], cwd=ROOT, check=True)
