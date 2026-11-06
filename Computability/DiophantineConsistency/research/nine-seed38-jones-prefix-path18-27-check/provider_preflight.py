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
q = D / 'reviews/nine-seed38-jones-prefix-path18-20-terminal-frontier-independent'
if sha(q / 'check.py') != '274762e7159b0a7f4677fa0b37cdd8938e9bccee7c86a2768d0ba847a4a45aaa' or sha(q / 'result.json') != '612da7924995b22efc9fe4c9ba175e82b7bb65850856ba7f48bfdc7671da4677':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-path18-27-draft'
if sha(draft / 'Norm38MacroPath18to27.lean') != 'efae242aed7e8139a7fe5c4adc67bbc8574fefa2830a02bee7b5cdfccfd3fb18': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-prefix-path18-20-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPath18to20.olean'
expected = '0a55af76feec76743016a3c845bf21053e3aa52312deb2a98db9229adf745e41'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPath18to27.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPath18to20': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and concrete d18-to-d27 path source; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
