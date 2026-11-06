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
q = D / 'reviews/nine-seed38-jones-prefix-group03-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '7ff8505e755090bf5b29abe4b074bcd36546ed597cc43405b9e4ea6a87c72745' or sha(q / 'result.json') != '2742892c8e514ac28db872993d219c639faf84961fd18f4852a03e01de81c8e3':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-group04-draft'
for name, digest in (('Norm38MacroPrefixInputsA.lean','b9bbb4824dc8add66023e9ff695bc2541967548c137607a55d197d9104f58101'),('Norm38MacroPrefixInputsB.lean','262efba661c8dde99a92eeba9f3bb3fba79da9700554d3cda42525caefc341bc')):
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPrefixGlarge.olean'
expected = 'b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPrefixInputsA.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPrefixGlarge': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and two symbolic input-prefix source files; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
