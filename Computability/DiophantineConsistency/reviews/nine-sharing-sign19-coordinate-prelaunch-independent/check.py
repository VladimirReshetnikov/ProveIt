#!/usr/bin/env python3
"""Review E lift, drop and coordinate recovery before Lean execution."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign19-coordinate-check'
draft = research/'nine-sharing-sign19-model-bridge-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet/'src/DiophantineConsistency/Sign19Coordinate.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign19Coordinate'
assert digest(src) == digest(draft/'Sign19Coordinate.lean') == entry['source_sha256']
s = src.read_text()
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M) == entry['imports'] == ['DiophantineConsistency.SharingSign19Squares','DiophantineConsistency.SharingSign20Squares']
lift = s.split('def lift ',1)[1].split('![',1)[1].split(']',1)[0]
drop = s.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0]
lc = [x.strip() for x in lift.split(',')]
dc = [x.strip() for x in drop.split(',')]
assert lc[:15] == [f'v {i}' for i in range(15)] and lc[16:] == [f'v {i}' for i in range(15,20)]
assert lc[15] == '(v 8 + 1) * ((beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1))'
assert dc == [f'v {i}' for i in range(15)] + [f'v {i}' for i in range(16,21)]
assert 'SharingSeed20Degree20.firstResidual p' in s
assert 'SharingSign20Squares.seed_zero_iff_residuals' in s and 'ι_injective' in s
assert all(('theorem '+n) in s for n in ('y_zero','y_coordinate','lift_drop'))
assert s.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 3
r=(packet/'run.py').read_text()
assert digest(packet/'run.py') == '604d5dee365c1d6b9784fa3f2f2086d165ce77afdf74f4ade3f6a3df43de9fb7'
assert "if local=='SharingSign19Squares':" in r and "elif local in observed['observed']:" in r
assert "for name,rec in observed['observed'].items():" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
for review in ('nine-sharing-sign19-staged-syntax-terminal-independent','nine-sharing-sign20-seed-squares-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'lift_arity':len(lc),'drop_arity':len(dc),'scope':'source/provider check only; no Lean coordinate theorem or full bridge'},sort_keys=True,indent=2))
