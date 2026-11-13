#!/usr/bin/env python3
"""Review normalized-S lift, drop and coordinate recovery before Lean execution."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign21-coordinate-check'
draft = research/'nine-sharing-sign21-model-bridge-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet/'src/DiophantineConsistency/Sign21Coordinate.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign21Coordinate'
assert digest(src) == digest(draft/'Sign21Coordinate.lean') == entry['source_sha256']
s = src.read_text()
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M) == entry['imports'] == ['DiophantineConsistency.SharingSign21Squares','DiophantineConsistency.SharingSign22Squares']
lift = s.split('def lift ',1)[1].split('![',1)[1].split(']',1)[0]
drop = s.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0]
lc = [x.strip() for x in lift.split(',')]
dc = [x.strip() for x in drop.split(',')]
assert lc[:21] == [f'v {i}' for i in range(21)] and lc[22:] == ['v 21']
assert lc[21] == '(v 6 + 1) * (v 17 * (v 17 + 2))'
assert dc == [f'v {i}' for i in range(21)] + ['v 22']
assert '((SharingSeed22Dodecic.remainingResiduals p).drop 8).head? = some (oldS p)' in s
assert 'SharingSign22Squares.seed_zero_iff_residuals' in s and 'ι_injective' in s
assert all(('theorem '+n) in s for n in ('old_s_row','s_zero','s_coordinate','lift_drop'))
assert 'hp0' not in s and 'Sign21Transfers' not in s
for review in ('nine-sharing-sign21-seed-squares-terminal-independent','nine-sharing-sign22-seed-squares-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'lift_arity':len(lc),'drop_arity':len(dc),'scope':'source/provider check only; no Lean coordinate theorem or full bridge'},sort_keys=True,indent=2))
