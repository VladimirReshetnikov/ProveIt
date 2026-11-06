#!/usr/bin/env python3
"""Recheck exact named-prefix producer and generated proof source; no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
q = D / 'reviews/nine-seed38-jones-prefix-group02-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '0491edf9eadfba7404f118c6445482ed6245560fe873f7f19ccdfaea99b4fa32' or sha(q / 'result.json') != 'f5c72aa2d5225957dafe9e3779feb803d2f0ddef8a725349e3a93b63ecc6b516':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-group03-staged-draft'
if sha(draft / 'split.py') != '6cf82731d41c8c37f282635f79cdb5f4f883f4277ffb89ea851679541258c3fa' or sha(draft / 'Norm38MacroPrefixCarry03.lean') != '22dc3497bf7c376eb505518e806bec65e98168a77d5185b3f1f331ad192de7ec':
    raise RuntimeError('source pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(draft / 'split.py'), '--check'], capture_output=True, timeout=30)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_MECHANICAL_STAGE_SPLIT_ONLY':
    raise RuntimeError(('chain generation', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-prefix-group02-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPrefixCarry.olean'
expected = '8800799bae0f3693aed496121077ca33d4b2ce5686dc7621e158a0a8d5bedc0e'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPrefixCarry03.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPrefixCarry': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and mechanical source split; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
