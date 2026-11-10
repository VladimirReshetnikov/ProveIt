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
packet = research/'nine-sharing-sign19-zero-assembly-check'
draft = research/'nine-sharing-sign19-zero-assembly-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign19ForwardBridge','Sign19ReverseBridge']
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
contents = []
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
    contents.append(src.read_text())
assert rows[0]['imports'] == ['DiophantineConsistency.Sign19Transfers00','DiophantineConsistency.Sign19Transfers01']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign19ForwardBridge']
gates = ['main_root','Dc2','tau','N0','Nt','cTminusR','V','V2minusY2','Na','scaled_Ns']
fwd,rev = contents
old_rows = fwd.split('theorem old_rows ',1)[1].split(':= by rfl',1)[0]
new_rows = rev.split('theorem new_rows ',1)[1].split(':= by rfl',1)[0]
assert re.findall(r'Sign19Transfers.old(\w+) p',old_rows) == gates
assert re.findall(r'Sign19Transfers.new(\w+) p',new_rows) == gates
assert old_rows.count('SharingSeed20Degree20.firstResidual p') == 2
assert 'Sign19Coordinate.y_zero p beta v hp0' in fwd and 'Sign19Coordinate.lift_drop p beta v hp0 hz' in rev
for gate in gates:
    assert f'Sign19Transfers.{gate}_eval p beta v hp0)).mpr' in fwd
    assert f'Sign19Transfers.{gate}_eval p beta (Sign19Coordinate.drop v) hp0)).mp' in rev
assert all('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in t for t in (fwd,rev))
upstream = root/'reviews/nine-sharing-sign19-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
runner=packet/'run.py';assert digest(runner)=='1acd6b1e4281aa5ca2794e8af3cd5b3cff024cdd102911e9256552206d92afcd'
r=runner.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "matches=[x for x in state['rows'][:-1] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','old_rows':11,'new_rows':10,'runner_sha256':digest(packet/'run.py'),
                  'scope':'conditional Y lift/drop assembly proposal; no Lean result or endpoint'},sort_keys=True,indent=2))
