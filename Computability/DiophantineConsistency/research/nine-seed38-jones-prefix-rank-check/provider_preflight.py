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
q = D / 'reviews/nine-seed38-jones-prefix-group06-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '01622fbcbfa5117f12235b3fdde4d89be88916be1e829d29e27c3b5bd37ea885' or sha(q / 'result.json') != '64f4c6b74b13a3600bbfee4805bbf3f084c9254b3b0b87e5f11c90464a316a1d':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-rank-draft'
for name, digest in (('Norm38MacroRankRaw.lean','a22def05d850d3bddb2685a45f016493ae3a10b9b931d2b137039ba9209ecfe6'),('Norm38MacroRankCarry.lean','258d07601bdeaffaf681fdaf1b5f549e055fcf3d991ddc231cb95115d8b04cf2')):
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-prefix-group06-staged-check-20261106/lib/DiophantineConsistency')
selected = {}
for n, expected in [('Norm38MacroPrefixCarrySums','789438afddf47cad95d8657dd0d029f284fa9d3a02dc99ab33275214ffe70eb2'),('Norm38MacroPrefixCarryOthers','9cc1239aeeff42841ca5d2f71796aeb859846dcefd4992fce2417e879f804279')]:
    obj = base / (n + '.olean')
    if not obj.is_file() or sha(obj) != expected: raise RuntimeError(('provider', n))
    selected['DiophantineConsistency.'+n] = {'realpath': str(obj.resolve()), 'sha256': expected}
for n in ['Norm38MacroRankRaw','Norm38MacroRankCarry']:
    if os.path.lexists(base / (n+'.olean')): raise RuntimeError(('output shadows provider',n))
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,
                  'scope':'Audited prefix producers and symbolic rank sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
