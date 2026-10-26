#!/usr/bin/env python3
"""Check each independent candidate against the included exact baseline fixtures."""
import json
import pathlib
import subprocess
import sys

package = pathlib.Path(__file__).resolve().parents[1]
rows = []
for patch in sorted((package / 'patches').glob('*.patch')):
    proc = subprocess.run(['git', 'apply', '--check', str(patch)],
                          cwd=package / 'baseline', text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    rows.append({'patch': patch.name, 'exit_code': proc.returncode,
                 'output': proc.stdout.strip()})
print(json.dumps(rows, indent=2))
sys.exit(0 if all(x['exit_code'] == 0 for x in rows) else 1)
