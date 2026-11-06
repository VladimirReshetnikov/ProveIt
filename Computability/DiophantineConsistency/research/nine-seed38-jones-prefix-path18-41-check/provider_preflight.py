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
q = D / 'reviews/nine-seed38-jones-prefix-path18-34-terminal-frontier-independent'
if sha(q / 'check.py') != 'c53e049dd60cd081fbf49a390b6147312b8821d71bf9e5e5e458345b4551ccb8' or sha(q / 'result.json') != '2a3386987970523092358d7122da0e021bc6a5d48eb4b0f39f6db2abd01617fa':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-path18-41-draft'
if sha(draft / 'Norm38MacroPath18to41.lean') != '2dff4ff4b5b7b8bdeb10a03410b51857a47d50c966efcaa0d4fdb98da30e31bb': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-prefix-path18-34-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPath18to34.olean'
expected = '25eb31cce810ce42e877e0a36c274999d5344eba255901e8ab828d7905934dae'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPath18to41.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPath18to34': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and concrete d18-to-d41 path source; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
