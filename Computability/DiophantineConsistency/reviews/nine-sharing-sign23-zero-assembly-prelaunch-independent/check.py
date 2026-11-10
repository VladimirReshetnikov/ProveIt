#!/usr/bin/env python3
"""Review sign23 Delta forward/reverse zero assembly proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign23-zero-assembly-check'
draft = research/'nine-sharing-sign23-zero-assembly-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign23ForwardBridge','Sign23ReverseBridge']
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
contents = []
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
    contents.append(src.read_text())
assert rows[0]['imports'] == ['DiophantineConsistency.Sign23Transfers00','DiophantineConsistency.Sign23Transfers01']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign23ForwardBridge']
gates = ['Y','E','kY','main_root','Dc2','tau','N0','Nt','cTminusR','V','normalized_S','V2minusY2','Na','scaled_Ns']
fwd,rev = contents
old_rows = fwd.split('theorem old_rows ',1)[1].split(':= by rfl',1)[0]
new_rows = rev.split('theorem new_rows ',1)[1].split(':= by rfl',1)[0]
assert re.findall(r'Sign23Transfers.old(\w+) p',old_rows) == gates
assert re.findall(r'Sign23Transfers.new(\w+) p',new_rows) == gates
assert old_rows.count('Sign23Coordinate.oldDelta p') == 1
assert 'Sign23Coordinate.delta_zero p v' in fwd and 'Sign23Coordinate.lift_drop p v hz' in rev
for gate in gates:
    assert f'Sign23Transfers.{gate}_eval p v)).mpr' in fwd
    assert f'Sign23Transfers.{gate}_eval p (Sign23Coordinate.drop v))).mp' in rev
assert 'hp0' not in fwd+rev
upstream = root/'reviews/nine-sharing-sign23-transfers-retry01-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','old_rows':15,'new_rows':14,'runner_sha256':digest(packet/'run.py'),
                  'scope':'natural Delta lift/drop assembly proposal; no Lean result or endpoint'},sort_keys=True,indent=2))
