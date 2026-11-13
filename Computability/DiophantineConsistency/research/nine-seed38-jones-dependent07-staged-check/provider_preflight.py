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
q = D / 'reviews/nine-seed38-jones-dependent06-staged-terminal-frontier-independent'
if sha(q / 'check.py') != 'aee8eeb61486a0934005bf30a063c14d2e297f326192338f5f480b53ffea7044' or sha(q / 'result.json') != '78a88923ba6fb795e7638241878dab3603dc19ea664aba10291ae8b115cc6bfd':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent07-draft'
for name, digest in [('Norm38MacroDependentI.lean', '716b1b31e873561f9490e903d6e4f7b2b24b89d0958d54ea2fea15abd57519c7'), ('Norm38MacroDependentA0Early.lean', '8a0a39e304e5321c1bc3e33f3299462792c4d6ac57943b8b769fad9dc243943d'), ('Norm38MacroDependentA0.lean', 'f481670fd4ea6c06b102b6c43d65b67116ee98d077687f5ccc92760ff789087f'), ('Norm38MacroDependentA1.lean', '2e1fff89404888e30e2c4ac01f9a52220612b83b7b1231292fd37d0713e1456c'), ('Norm38MacroDependentV.lean', 'd39cbafb286d71e7e98c5d5b56d97fd08081d53dfcf2b7d2da08b781c0f858f5')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent06-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentH.olean'
expected = 'fd1691414fc25dab60414cdb181d1c92bcacffc621ee3fb19a6804008d4850ce'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentI.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentH': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and I/A0/A1/V dependent-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
