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
q = D / 'reviews/nine-seed38-jones-prefix-group05-terminal-frontier-independent'
if sha(q / 'check.py') != 'be57dc896c38e9f6e029d57041979a7edbfdcbed32d857ed97d877018141f423' or sha(q / 'result.json') != '983d494267643fd48718d104fe302405b7b2d5ea705b00abaf7854594849dbbb':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-group06-draft'
for name, digest in (('Norm38MacroPrefixCarrySums.lean','55adbc07f19d6493e3234f5755e4c19acfd641f9880b0e05cefbaeabcc56ee37'),('Norm38MacroPrefixCarryOthers.lean','4f7ce529c5dc858ec7e0bed631228100a9561c1c8b2a6855a4907ed9b457006b')):
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-prefix-group05-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPrefixQNCarry.olean'
expected = 'bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPrefixCarrySums.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPrefixQNCarry': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and seven remaining preservation cuts; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
