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
q = D / 'reviews/nine-seed38-jones-dependent01-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '428e5c4a81481b076a9a3ac8e48de105b6743df9c3ab9669a1c90020b55c6f8b' or sha(q / 'result.json') != '8729babe68c3fe7f3a27d58af564586d5e3d6e8f9e822fb806c8f9c8ba6d4a43':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent02-draft'
for name, digest in [('Norm38MacroDependentM.lean', 'be513db9d34caa379a6b6e8d82132bb7cc160eda825ff0d08f42c1dc471db4cd'), ('Norm38MacroDependentP.lean', '9269263c385f49d15b17ea935a29c1f9ef29887526a7c8f6ac26150da233085d'), ('Norm38MacroDependentK.lean', 'edcdeb31d604966e84461cf1b5fa466383c49392040ebb915a6551eaf07e5498')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent01-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentY.olean'
expected = 'eb28e13077c175963702682ff8501cb25c4036813d5d035c3574a9e605f516a9'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentM.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentY': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and M/P/K dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
