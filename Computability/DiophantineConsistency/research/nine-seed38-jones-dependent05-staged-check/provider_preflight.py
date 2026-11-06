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
q = D / 'reviews/nine-seed38-jones-dependent04-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '5962b78b76c806f9dc152d2eb8bef8c7faa6699b43293dee30236b1f18d9ed12' or sha(q / 'result.json') != '3e7d2596e95f280c96ae7e8da8379731390b8db4116fb27fcd3edec9d9db800d':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent05-draft'
for name, digest in [('Norm38MacroDependentIcarry.lean', '7fcdddc9b330d21af36451580d0ae84071b9f60d7599bb5e08f3c3a777d26d93'), ('Norm38MacroDependentE.lean', 'fbf201b90ba60749ab0296f78fb187934b5abc254c0f364b839965b23dbdbdfc'), ('Norm38MacroDependentF.lean', '092e73eb39f9bd08c4e21ee0b82fe0fcc85ceb18cd5f2bab7505c87f2d3aa79e')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent04-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentD.olean'
expected = '3fb3464ef223d9d0e7dc33fccd7d1845337aea9ccc9184c137e6664bc2026931'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentIcarry.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentD': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and E/F dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
