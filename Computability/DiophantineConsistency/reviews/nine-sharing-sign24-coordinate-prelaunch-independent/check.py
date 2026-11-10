#!/usr/bin/env python3
"""Review q3 lift, drop and the beta hypothesis before Lean execution."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign24-coordinate-check'
draft = research / 'nine-sharing-sign24-model-bridge-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet / 'src/DiophantineConsistency/Sign24Coordinate.lean'
data = src.read_text()
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert len(manifest) == 1 and manifest[0]['module'] == 'DiophantineConsistency.Sign24Coordinate'
assert digest(src) == digest(draft / 'Sign24Coordinate.lean') == manifest[0]['source_sha256']
assert manifest[0]['imports'] == ['DiophantineConsistency.SharingSign24Squares', 'DiophantineConsistency.SharingSign25Squares']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$', data, re.M) == manifest[0]['imports']
lift = data.split('def lift ', 1)[1].split('![', 1)[1].split(']', 1)[0]
drop = data.split('def drop ', 1)[1].split('![', 1)[1].split(']', 1)[0]
lc = [x.strip() for x in lift.split(',')]
dc = [x.strip() for x in drop.split(',')]
assert lc[:15] == [f'v {i}' for i in range(15)] and lc[16:] == [f'v {i}' for i in range(15,25)]
assert lc[15] == '(beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1)'
assert dc == [f'v {i}' for i in range(15)] + [f'v {i}' for i in range(16,26)]
assert data.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 3
assert 'SharingSign25Squares.seed_zero_iff_residuals' in data and 'ι_injective' in data
assert all(('theorem ' + n) in data for n in ('q3_zero', 'q3_coordinate', 'lift_drop'))
assert 'Sign24Transfers' not in data
syntax = root / 'reviews/nine-sharing-sign24-seed-squares-terminal-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(syntax)], check=True, capture_output=True, timeout=120)
sign25 = root / 'reviews/nine-sharing-sign25-seed-squares-terminal-frontier-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(sign25)], check=True, capture_output=True, timeout=120)
preflight = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'], capture_output=True, text=True, timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH', 'source_sha256':digest(src), 'runner_sha256':digest(packet / 'run.py'),
                  'beta_model_cast':'explicit hp0 in all three theorems', 'lift_arity':len(lc), 'drop_arity':len(dc),
                  'scope':'source and provider point checks only; no Lean bridge or endpoint'}, sort_keys=True, indent=2))
