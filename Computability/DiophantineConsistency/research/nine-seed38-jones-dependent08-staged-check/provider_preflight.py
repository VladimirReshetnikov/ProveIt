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
q = D / 'reviews/nine-seed38-jones-dependent07-staged-terminal-frontier-independent'
if sha(q / 'check.py') != '3131f0ac15437151abbf12ec026b35630df58542d0b1d4f4f63dc3dc14f169a8' or sha(q / 'result.json') != '6dea09a5229acfc79d3dc1afa8380370ae173632b4cbde02acec4e12e452b3f9':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-dependent08-draft'
for name, digest in [('Norm38MacroDependentBdCd.lean', '221a8bf6adbf8bab68c537caf7d2ade52c0602d03f12a090d4c8483edfeb74d7'), ('Norm38MacroDependentDmKc.lean', '836bbad65ae08ec2f70cc0c8af8eb600cccd81ccca7456083be4d88a39c03396'), ('Norm38MacroDependentOutput.lean', 'f2448afc57fa19d371082e6ecdc2b968fdb1af1792389abd1995845de9c87e27')]:
    if sha(draft / name) != digest: raise RuntimeError(('source pin', name))
base = Path('/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroDependentV.olean'
expected = '93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroDependentBdCd.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroDependentV': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and final six local-prefix sources; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
