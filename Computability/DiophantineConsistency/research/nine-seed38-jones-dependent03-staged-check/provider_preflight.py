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
q = D / 'reviews/nine-seed38-jones-dependent02-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '3fe72c765d785e759248768d743b1f948b2d7ec4146d2d981a938348f06d6bcb' or sha(q / 'result.json') != '03f4dd834eb2b106f48865c044c6614712d4f52487540cf6a717f70f8f7375fd':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent03-draft'
for name, digest in [('Norm38MacroDependentA.lean', 'df249e2bccb4954d892b1c3d4caf49be93c9fdc9dab1a5a4995191228279e764'), ('Norm38MacroDependentBprime.lean', '5f12c9049e6d7a3cf96d69bca30b1fc891d7723af6015977c04362540ef32488'), ('Norm38MacroDependentW.lean', 'f8d2767d21bee193c7433cf47f97f971443946da1217faf4e3693be9abbc4dec'), ('Norm38MacroDependentC.lean', '1d95bf9e6811645e6a7ba8e96713e4089974f5925dff05601a26f130386cef93')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent02-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentK.olean'
expected = '54542c0eb712eb19b70ae07aef9308156edf7fc4311e177d00fb8181278a5f9d'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentA.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentK': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and A/Bprime/W/C dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
