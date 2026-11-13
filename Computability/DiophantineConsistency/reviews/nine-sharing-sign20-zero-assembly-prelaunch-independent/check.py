#!/usr/bin/env python3
"""Review sign20 conditional E forward/reverse zero assembly proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign20-zero-assembly-check'
draft = research/'nine-sharing-sign20-zero-assembly-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign20ForwardBridge','Sign20ReverseBridge']
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
contents = []
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
    contents.append(src.read_text())
assert rows[0]['imports'] == ['DiophantineConsistency.Sign20Transfers00','DiophantineConsistency.Sign20Transfers01']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign20ForwardBridge']
gates = ['Y','main_root','Dc2','tau','N0','Nt','cTminusR','V','V2minusY2','Na','scaled_Ns']
fwd,rev = contents
old_rows = fwd.split('theorem old_rows ',1)[1].split(':= by rfl',1)[0]
new_rows = rev.split('theorem new_rows ',1)[1].split(':= by rfl',1)[0]
assert re.findall(r'Sign20Transfers.old(\w+) p',old_rows) == gates
assert re.findall(r'Sign20Transfers.new(\w+) p',new_rows) == gates
assert old_rows.count('Sign20Coordinate.oldE p') == 1
assert 'Sign20Coordinate.e_zero p beta v hp0' in fwd and 'Sign20Coordinate.lift_drop p beta v hp0 hz' in rev
for gate in gates:
    assert f'Sign20Transfers.{gate}_eval p beta v hp0)).mpr' in fwd
    assert f'Sign20Transfers.{gate}_eval p beta (Sign20Coordinate.drop v) hp0)).mp' in rev
assert all('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in t for t in (fwd,rev))
upstream = root/'reviews/nine-sharing-sign20-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','old_rows':12,'new_rows':11,'runner_sha256':digest(packet/'run.py'),
                  'scope':'conditional E lift/drop assembly proposal; no Lean result or endpoint'},sort_keys=True,indent=2))
