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
q = D / 'reviews/nine-seed38-jones-prefix-group01-retry01-terminal-frontier-independent'
if sha(q / 'check.py') != '3eadeed7fc8014c96bd3eda7aa0e697a07ce84124dafc4bfe13acff7c19e2f36' or sha(q / 'result.json') != '1b482adfa9f7375b7a508de7a76890f2bc3760ab73f9920997f63e92f552deba':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-group02-staged-draft'
if sha(draft / 'split.py') != '3e383bfe57f0315d83c791359a66a90c4847eb8f42c60f26a0028fb98ab2111b' or sha(draft / 'Norm38MacroPrefixCarry.lean') != '7d99a72b7c27c335f4e8c0f2e5a66468c907c8321dce03259a4e13cd456e2d3e':
    raise RuntimeError('source pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(draft / 'split.py'), '--check'], capture_output=True, timeout=30)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_MECHANICAL_STAGE_SPLIT_ONLY':
    raise RuntimeError(('chain generation', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-prefix-group01-retry01-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroPrefixGroup01.olean'
expected = 'a312303ac1f6f1ce780ec12a4f74a8633a22ca6e1779feb675ef6edc8674186a'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPrefixCarry.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroPrefixGroup01': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and mechanical source split; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
