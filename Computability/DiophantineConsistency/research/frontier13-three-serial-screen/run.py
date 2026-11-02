#!/usr/bin/env python3
"""Capture two heuristic screen executions and their actual process exits."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
screen, output = HERE / 'screen.py', HERE / 'receipt.json'
if output.exists() or output.is_symlink():
    raise RuntimeError('refusing to overwrite receipt')
files = [screen, RESEARCH/'adaptive-square-sums/candidate.json',
         RESEARCH/'adaptive-direct-ordinate86/candidate.json']
hashes = {str(p.relative_to(RESEARCH)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
runs = []
for graph in files[1:]:
    result = subprocess.run([sys.executable, str(screen), str(graph)], capture_output=True,
                            text=True, timeout=180)
    if result.returncode != 0 or 'CANDIDATE' in result.stdout or not result.stdout.rstrip().endswith('done; modular signature screening only'):
        raise RuntimeError(('unexpected heuristic screen outcome', str(graph), result.returncode,
                            result.stdout, result.stderr))
    runs.append({'graph': str(graph.relative_to(RESEARCH)), 'exit_code': result.returncode,
                 'stdout': result.stdout, 'stderr': result.stderr})
optimized = subprocess.run([sys.executable, '-O', str(screen), str(files[1])], capture_output=True,
                           text=True, timeout=30)
if optimized.returncode == 0 or 'optimized Python is unsupported' not in optimized.stderr:
    raise RuntimeError(('optimized guard failed', optimized.returncode, optimized.stderr))
if hashes != {str(p.relative_to(RESEARCH)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}:
    raise RuntimeError('an input changed during screening')
receipt = {'status':'PASS_HEURISTIC_THREE_SERIAL', 'inputs_sha256':hashes, 'runs':runs,
           'optimized':{'exit_code':optimized.returncode, 'guard_message':'optimized Python is unsupported'},
           'scope':'Modular three-gate serial heuristic; exclusions and no minimum claim apply.'}
output.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS_HEURISTIC_THREE_SERIAL', hashlib.sha256(output.read_bytes()).hexdigest())
