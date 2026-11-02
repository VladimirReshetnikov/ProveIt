#!/usr/bin/env python3
"""Capture actual bounded-shear checker exits without overwriting evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
check, output = HERE/'check.py', HERE/'receipt.json'
if output.exists() or output.is_symlink(): raise RuntimeError('refusing to overwrite receipt')
before = hashlib.sha256(check.read_bytes()).hexdigest()
normal = subprocess.run([sys.executable,str(check)],capture_output=True,text=True,timeout=60)
optimized = subprocess.run([sys.executable,'-O',str(check)],capture_output=True,text=True,timeout=60)
if normal.returncode != 0 or not normal.stdout.startswith('PASS_BOUNDED_SHEAR_DEGREE '):
    raise RuntimeError(('normal check failed',normal.returncode,normal.stdout,normal.stderr))
if optimized.returncode == 0 or 'optimized Python is unsupported' not in optimized.stderr:
    raise RuntimeError(('optimized guard failed',optimized.returncode,optimized.stderr))
if hashlib.sha256(check.read_bytes()).hexdigest() != before: raise RuntimeError('checker changed during run')
result = json.loads(normal.stdout.split(' ',1)[1])
receipt = {'status':'PASS_BOUNDED_SHEAR_OBSTRUCTION', 'checker_sha256':before,
           'normal':{'exit_code':normal.returncode,'result':result,'stderr':normal.stderr},
           'optimized':{'exit_code':optimized.returncode,'guard_message':'optimized Python is unsupported'},
           'scope':'Bounded witness-degree shears only; finite integer reasoning, not Lean or minimality.'}
output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('PASS_BOUNDED_SHEAR_OBSTRUCTION',hashlib.sha256(output.read_bytes()).hexdigest())
