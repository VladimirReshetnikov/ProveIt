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
q = D / 'reviews/nine-seed38-jones-prefix-path18-41-terminal-frontier-independent'
if sha(q / 'check.py') != '470ff900fab224abe16c3c5e81cc51dc52f07dd62a8877c4fe2953b8b4392cba' or sha(q / 'result.json') != '15fc98fc031182f5550ba6a135b2fe86d5b26f18896492192acab6da412f76e4':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-path18-45-draft'
if sha(draft / 'Norm38MacroPath18to45.lean') != '046e61d86f88b61d713475b1355d3fa9692547a9469928cba09f644d53229c6e': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-prefix-path18-41-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPath18to41.olean'
expected = 'b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPath18to45.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPath18to41': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and concrete d18-to-d45 path source; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
