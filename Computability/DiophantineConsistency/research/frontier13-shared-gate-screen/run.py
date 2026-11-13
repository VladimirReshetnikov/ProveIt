#!/usr/bin/env python3
"""Capture observed shared-gate screen outcomes without overwriting evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
screen, output = HERE / 'screen.py', HERE / 'receipt.json'
if output.exists() or output.is_symlink():
    raise RuntimeError('refusing to overwrite receipt')
before = hashlib.sha256(screen.read_bytes()).hexdigest()
normal = subprocess.run([sys.executable, str(screen)], capture_output=True, text=True, timeout=60)
optimized = subprocess.run([sys.executable, '-O', str(screen)], capture_output=True, text=True, timeout=60)
if normal.returncode != 0 or json.loads(normal.stdout)['status'] != 'PASS_SHARED_GATE_SCREEN':
    raise RuntimeError(('normal screen failed', normal.returncode, normal.stdout, normal.stderr))
if optimized.returncode == 0 or 'this certificate requires Python assertions enabled' not in optimized.stderr:
    raise RuntimeError(('optimized guard failed', optimized.returncode, optimized.stderr))
if hashlib.sha256(screen.read_bytes()).hexdigest() != before:
    raise RuntimeError('screen source changed during run')
receipt = {'status': 'PASS_BOUNDED_SHARED_GATE_SCREEN', 'screen_sha256': before,
           'normal': {'exit_code': normal.returncode, 'result': json.loads(normal.stdout),
                      'stderr': normal.stderr},
           'optimized': {'exit_code': optimized.returncode,
                         'guard_message': 'this certificate requires Python assertions enabled'},
           'scope': 'Two retained target gates sharing one earlier or new intermediate; universal-port target identities only.'}
output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print('PASS_BOUNDED_SHARED_GATE_SCREEN', hashlib.sha256(output.read_bytes()).hexdigest())
