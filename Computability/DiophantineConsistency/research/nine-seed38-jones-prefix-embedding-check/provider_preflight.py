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
q = D / 'reviews/nine-seed38-jones-compact-semantics-cut-terminal-frontier-independent'
if sha(q / 'check.py') != '07982eeff551c60200f490bd36a36781c6630cc791739974c9ec3fba7e1339db' or sha(q / 'result.json') != '93813e1c820304ff903147c035c6a5ed50cd4f87bfd9d64e24330700454f1af5':
    raise RuntimeError('terminal audit pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
    raise RuntimeError(('terminal audit failed', r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-prefix-embedding-draft'
if sha(draft / 'Norm38MacroPrefixEmbedding.lean') != '0e44abd4d3cbc028dac5759b7091c3e861376f42f6327a4db11c1512ede71477': raise RuntimeError('source pin')
base = Path('/tmp/nine-seed38-jones-compact-semantics-cut-check-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroCuts.olean'
expected = '9c83339175c439edd66ef5a10e6a192b79621803463dbf9e8420fc6f8725bf36'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('first-prefix provider')
if os.path.lexists(base / 'Norm38MacroPrefixEmbedding.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroCuts': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited prefix producer and generic prefix-embedding source; no Lean, full recipe semantics, JSON binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
