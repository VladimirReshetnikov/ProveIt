#!/usr/bin/env python3
"""Recheck named-formula semantics producer and route; no Lean."""
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
q = D / 'reviews/nine-seed38-jones-compact-recipe-terminal-frontier-independent'
if sha(q / 'check.py') != '1ed31a4f69b3f22cfef198481866e4917cd4785fa0ba9d025551b2d860a9778f' or sha(q / 'result.json') != '333840041f59cdb95b8c85e07cd25d2a3448a14e4fee2a5a267c6e2ca3e4f46a':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-compact-recipe-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroRecipe.olean'
expected = 'c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('macro recipe provider')
if os.path.lexists(base / 'Norm38MacroScoped.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroRecipe': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited direct provider and route; no Lean, graph semantics or complete dynamic ancestry.'}, indent=2, sort_keys=True))
