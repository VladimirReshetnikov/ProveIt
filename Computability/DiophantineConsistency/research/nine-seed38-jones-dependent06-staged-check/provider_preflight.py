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
q = D / 'reviews/nine-seed38-jones-dependent05-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '4a0b38cafb87dfdbaf3e0aa4c8038f1d0f595992903814632316b4dd80988bed' or sha(q / 'result.json') != '032d6f20599ed912ba688e6fbe24697fd7ec8a5742df1b9de9442f2f653b1f44':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent06-draft'
for name, digest in [('Norm38MacroDependentJcarry.lean', '5e864344f5860ee5bd75714b659e7ab98c3612bbb1b24518a111a74ef58dab14'), ('Norm38MacroDependentGprime.lean', 'c8d711411765540c03e40c2b4f63d42c2d3869bf172c9d77e7ee60b1a6a5e103'), ('Norm38MacroDependentHcarry.lean', 'ffb70f75f4a4dee7ba85515ad2390c27523bb9eb44e25de15a456984de41e577'), ('Norm38MacroDependentH.lean', '3e6b8036faeb1bfd631ebc3439868f7e9ed332920edf38c7898e8df8e993fad9')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent05-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentF.olean'
expected = 'a7700d99911c457d906075eccae9433ac825b8b9fc0df269c01bfd66426b2118'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentJcarry.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentF': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and Gprime/H dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
