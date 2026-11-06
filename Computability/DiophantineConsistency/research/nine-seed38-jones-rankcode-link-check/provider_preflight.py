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
q = D / 'reviews/nine-seed38-jones-prefix-rank-retry01-terminal-frontier-independent'
if sha(q / 'check.py') != 'bccf2ded0c5b94d1db05b2cf219da33d5dbfe4068d42e86052554e0cff85c831' or sha(q / 'result.json') != 'c20513142a2b0dadd57f0dd9f9dc37a461b2f696342bc073d24e8442d44c5de3':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-rankcode-link-draft'
if sha(draft / 'Norm38MacroRankCodeLink.lean') != '4cfa6b974a6243ad55b2b311c4bc3049498cf7ef62cb9dc836e2ae7886918f43': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-prefix-rank-retry01-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroRankCarry.olean'
expected = '60217f4104203c8fde8da56182d932e5382b9b7b118962b8f0a392dd799e6c89'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroRankCodeLink.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroRankCarry': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and generic rank-polynomial link; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
