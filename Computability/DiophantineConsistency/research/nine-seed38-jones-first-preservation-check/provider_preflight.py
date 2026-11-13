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
q = D / 'reviews/nine-seed38-jones-named-prefix-terminal-frontier-independent'
if sha(q / 'check.py') != '569a2907627f46ad3c6bd8cdf9a2b081698ad65f08047f0a919c2f6ff3656a09' or sha(q / 'result.json') != '70430adb1ceb0bb52ca4248c9c8ac9ebad33c15dd1aab46ebf77b532811a8b70':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-first-preservation-draft'
if sha(draft / 'generate.py') != '56cd3e1c723ede6a7e00b77776e075dbb54b2fe5b4c07cc86a5fc18d79449e1d' or sha(draft / 'Norm38FirstPreservation.lean') != 'e164df6d225df13f13a69be44f52796dbdfb3bc0e3d193c1995ae175259b9de7':
    raise RuntimeError('source pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(draft / 'generate.py'), '--check'], capture_output=True, timeout=30)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_CHAIN_GENERATION_ONLY':
    raise RuntimeError(('chain generation', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-named-prefix-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPrefixFirst.olean'
expected = 'a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38FirstPreservation.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPrefixFirst': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and finite proof-chain generation; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
