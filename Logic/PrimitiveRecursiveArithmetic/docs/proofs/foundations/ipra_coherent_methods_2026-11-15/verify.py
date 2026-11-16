#!/usr/bin/env python3
"""Reproduce the finite exact-arithmetic diagnostics, not universal proofs."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
out = root / 'validation'
out.mkdir(exist_ok=True)
programs = [
    ('filtered_reference.py', 'filtered_checks.json'),
    ('check_weighted_norm.py', 'weighted_norm_checks.json'),
]
records = []
for program, result in programs:
    source = root / 'code' / program
    completed = subprocess.run(
        [sys.executable, str(source), str(out / result)],
        text=True, capture_output=True, check=False)
    (out / (source.stem + '_stdout.txt')).write_text(
        completed.stdout + completed.stderr)
    if completed.returncode:
        raise SystemExit(f'{program} failed: {completed.stderr}')
    records.append({'program': program, 'source_sha256': hashlib.sha256(
        source.read_bytes()).hexdigest(), 'exit_code': 0, 'result': result})
    print(f'{program}: passed')
payload = {'scope': 'Finite exact regression checks; not universal proofs.',
           'python_version': sys.version.split()[0], 'programs': records}
(out / 'python_checks.json').write_text(json.dumps(payload, indent=2) + '\n')
