#!/usr/bin/env python3
"""Run exact reference diagnostics and save observed results.

This is not an iPRA proof checker. The universal mathematical arguments and
the status of every Lean target are given in paper/report.pdf and CLAIMS.json.
"""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / 'validation'
RESULTS.mkdir(exist_ok=True)
checks = [('lex_reference.py', 'lex_checks.json'),
          ('plane_intersections.py', 'plane_checks.json'),
          ('auxiliary_envelope.py', 'auxiliary_checks.json')]
summary = []
for source, output in checks:
    run = subprocess.run([sys.executable, str(ROOT / 'code' / source)],
                         cwd=ROOT, text=True, capture_output=True, check=True)
    data = json.loads(run.stdout)
    if data.get('status') != 'passed':
        raise RuntimeError(f'{source}: unexpected status {data.get("status")}')
    (RESULTS / output).write_text(json.dumps(data, indent=2) + '\n')
    if run.stderr:
        (RESULTS / (output + '.stderr')).write_text(run.stderr)
    summary.append({'program': source, 'status': data['status'],
                    'output': 'validation/' + output})
    print(f'{source}: passed')
(RESULTS / 'python_summary.json').write_text(json.dumps({
    'status': 'passed', 'python_version': sys.version,
    'scope': 'finite exact arithmetic diagnostics; not universal proofs',
    'checks': summary}, indent=2) + '\n')
