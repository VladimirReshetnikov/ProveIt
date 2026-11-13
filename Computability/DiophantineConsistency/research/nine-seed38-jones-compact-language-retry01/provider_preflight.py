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
q = D / 'reviews/nine-seed38-jones-named-formula-terminal-frontier-independent'
if sha(q / 'check.py') != '19012c054315ad2215af375ced48d04a83aa2f76bb2a65045fc63d9d4b056751' or sha(q / 'result.json') != '213cc37a19e9d221f569a8ba7dbf09bca1ca6c12ca366dc2dbe4ca7af1e9d953':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-named-formula-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38NamedFormula.olean'
expected = 'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('named-formula provider')
if os.path.lexists(base / 'Norm38MacroLanguage.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38NamedFormula': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited direct provider and route; no Lean, graph semantics or complete dynamic ancestry.'}, indent=2, sort_keys=True))
