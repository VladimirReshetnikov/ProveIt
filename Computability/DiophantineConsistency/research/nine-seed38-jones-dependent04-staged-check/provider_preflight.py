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
q = D / 'reviews/nine-seed38-jones-dependent03-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '456db91d9870d3207907a5c115e33939ea1b423e46119ab658293beceafdb969' or sha(q / 'result.json') != '0d0d2aaa5960eeaec7200494b62a585de92ce9da175dbb32d245ea8b9eff25e0':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent04-draft'
for name, digest in [('Norm38MacroDependentJ.lean', '2e200102f2be0cceab613227249efd63c7921daa680f1e232724e11ae3af0d44'), ('Norm38MacroDependentQ.lean', 'a7a156db71800d5944572785885dc9ba2ba9d8d0e6e3a5a68cbd274e1c3cafe1'), ('Norm38MacroDependentD.lean', '796d65e5da039291ce773ac17bb0c132b18f12d6551aab61bb97095fa80958ee')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent03-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentC.olean'
expected = '8a69d181c2584313ff4add42d2197020e387b888cd676fbfa4dc465a305bd281'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentJ.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentC': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and J/Q/D dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
