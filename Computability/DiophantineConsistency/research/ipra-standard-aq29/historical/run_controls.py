#!/usr/bin/env python3
"""Record historical-parent toy controls; never use the real AQ29 parent."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[ROOT/'plan.py',ROOT/'extension/task-policy.json']+[HERE/name for name in (
    'prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py',
    'test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py',
    'test_full_chain.py','run_controls.py')]
before={str(p.resolve()):H(p) for p in files}
rows=[]
for name in ('test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py','test_full_chain.py'):
    p=subprocess.run([sys.executable,str(HERE/name)],cwd=HERE,capture_output=True,text=True,timeout=240)
    rows.append({'script':str((HERE/name).resolve()),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    if p.returncode:raise RuntimeError(('control failed',name,p.returncode,p.stdout,p.stderr))
if {str(p.resolve()):H(p) for p in files}!=before:raise RuntimeError('control inputs changed')
receipt={'status':'PASS_HISTORICAL_TOY_CONTROLS','inputs_sha256':before,'controls':rows,
         'scope':'Toy parent and sources only; no real AQ29 parent or endpoint replay.'}
output=HERE/'control-receipt.json'
if output.exists() or output.is_symlink():raise ValueError('refusing to overwrite control receipt')
output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('PASS_HISTORICAL_TOY_CONTROLS',len(rows),H(output))
