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
q = D / 'reviews/nine-seed38-jones-prefix-path18-27-terminal-frontier-independent'
if sha(q / 'check.py') != 'ef38d5e11c5b297fd7508dda863149d9e06b566d80071b6d07f10c440fd16857' or sha(q / 'result.json') != '01a162c25bee1b6b3b2dd1a6fe0eaae799b4d4437af347c4ee7854b886ea3ad9':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-path18-34-draft'
if sha(draft / 'Norm38MacroPath18to34.lean') != '3be3ce5b6535a492ff295bcdc0a54b9e8ed7addf860e60a0eb37bb80f39a6e34': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-prefix-path18-27-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPath18to34.olean'
expected = 'bf606152c9813c75de33752bb7c510814bf97c1cc2a3cb66faf2a6c56c48ee79'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPath18to34.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPath18to27': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and concrete d18-to-d34 path source; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
