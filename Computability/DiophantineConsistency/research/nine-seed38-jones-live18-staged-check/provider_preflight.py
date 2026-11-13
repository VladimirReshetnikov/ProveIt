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
q = D / 'reviews/nine-seed38-jones-prefix-rank-symbolic-terminal-frontier-independent'
if sha(q / 'check.py') != '2600cbf6e25f8d90ea0d2f4949af71902e31706e1cd3d8c69189f1a64b1a4407' or sha(q / 'result.json') != '0cb1533e9b380dff32ecebbc90586ed64175c4d65fbb22a3248a1c4fab941b7d':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-live18-draft'
for name, digest in [('Norm38MacroLive18Group01.lean', 'a218f74792b1c97d9c58fe4fa18b816392038faf89684649124e7389549a9d32'), ('Norm38MacroLive18Group02.lean', '37faad23da93c1f8c88bcd9fd7759f33b315b91b5f0996adb9c578cfe7b4e2c8'), ('Norm38MacroLive18Group03.lean', '7d753c75b74fe692481e447736b8bb83bbfe683b12c083ae1acbc32aeb286356'), ('Norm38MacroLive18Group04.lean', '57b121e8e47a5babed07ef2da168f96d679a7abeda421049de2c0261d45d300f')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-prefix-rank-symbolic-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroRankSymbolic.olean'
expected = 'b82180e10b4cf11a375cbfdcc3087eb69985c18473ae80a9eaf99ff2e8673408'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroLive18Group01.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroRankSymbolic': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and eleven live d18 preservation cuts; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
