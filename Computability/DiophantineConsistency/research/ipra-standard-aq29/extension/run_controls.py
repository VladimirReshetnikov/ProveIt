#!/usr/bin/env python3
"""Run and record toy controls only; this never builds the real endpoint."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
files = [ROOT/'plan.py', ROOT/'test_plan.py', ROOT/'draft/IPRAStandardAQ29.lean',
         ROOT/'draft/IPRAStandardAQ29Checks.lean'] + [HERE/name for name in (
    'prepare.py', 'freeze.py', 'rebuild.py', 'compare.py', 'run_pair.py',
    'task-policy.json', 'verify_fork.py', 'test_policy.py', 'test_prepare.py',
    'test_freeze.py', 'test_real_extension.py', 'test_full_chain.py', 'run_controls.py')]
before = {str(p.resolve()): H(p) for p in files}
commands = [(ROOT/'test_plan.py', ROOT), *[(HERE/name, HERE) for name in (
    'verify_fork.py', 'test_policy.py', 'test_prepare.py', 'test_freeze.py',
    'test_real_extension.py', 'test_full_chain.py')]]
rows = []
for script, cwd in commands:
    p = subprocess.run([sys.executable, str(script)], cwd=cwd, capture_output=True,
                       text=True, timeout=240)
    rows.append({'script': str(script.resolve()), 'exit_code': p.returncode,
                 'stdout': p.stdout, 'stderr': p.stderr})
    if p.returncode:
        raise RuntimeError(('control failed', str(script), p.returncode, p.stdout, p.stderr))
if {str(p.resolve()): H(p) for p in files} != before:
    raise RuntimeError('control inputs changed')
receipt = {'status': 'PASS_TOY_CONTROLS', 'inputs_sha256': before, 'controls': rows,
           'scope': 'Toy controls only; no real parent authentication or AQ29 proof replay.'}
output = HERE/'control-receipt.json'
if output.exists() or output.is_symlink():
    raise ValueError('refusing to overwrite control receipt')
output.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS_TOY_CONTROLS', len(rows), H(output))
