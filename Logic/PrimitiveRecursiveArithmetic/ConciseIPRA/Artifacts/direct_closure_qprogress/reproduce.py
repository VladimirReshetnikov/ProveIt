#!/usr/bin/env python3
"""Reproduce mathematical fixtures, process tests, and complete-source metrics."""
import json
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
commands = [(root / 'audit', [sys.executable, 'audit.py']),
            (root / 'compact', [sys.executable, 'verify.py', '--write'])]
results = []
for directory, command in commands:
    process = subprocess.run(command, cwd=directory, text=True, capture_output=True)
    results.append({'directory': directory.name, 'returncode': process.returncode,
                    'stdout': process.stdout, 'stderr': process.stderr})
    if process.returncode:
        print(process.stdout)
        print(process.stderr, file=sys.stderr)
        raise SystemExit(process.returncode)
(root / 'reproduction.json').write_text(json.dumps(
    {'python': sys.version, 'results': results}, indent=2) + '\n')
print('Reproduction completed: independent audit and compact-checker tests passed.')
