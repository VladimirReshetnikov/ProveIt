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
packet = research/'nine-sharing-sign17-zero-assembly-check'
draft = research/'nine-sharing-sign17-zero-assembly-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign17ForwardBridge','Sign17ReverseBridge']
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
contents = []
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
    contents.append(src.read_text())
assert rows[0]['imports'] == ['DiophantineConsistency.Sign17Transfer'+f'{i:02}' for i in range(8)]
assert rows[1]['imports'] == ['DiophantineConsistency.Sign17ForwardBridge']
gates = ['Dc2','tau','N0','Nt','cTminusR','V','Na','scaled_Ns']
fwd,rev = contents
old_rows = fwd.split('theorem old_rows ',1)[1].split(':= by rfl',1)[0]
new_rows = rev.split('theorem new_rows ',1)[1].split(':= by rfl',1)[0]
assert re.findall(r'Sign17Transfers.old(\w+) p',old_rows) == gates
assert re.findall(r'Sign17Transfers.new(\w+) p',new_rows) == gates
assert old_rows.count('Sign17Coordinate.oldD p') == 1
assert 'Sign17Coordinate.d_zero p v gap hg' in fwd and 'Sign17Coordinate.lift_drop v' in rev
for gate in gates:
    assert f'Sign17Transfers.{gate}_eval p v gap hg)).mpr' in fwd
    assert f'Sign17Transfers.{gate}_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp' in rev
assert '(hg : ι gap = ' in fwd and 'Sign17Coordinate.old_gap p v hz' in rev
upstream = root/'reviews/nine-sharing-sign17-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
runner=packet/'run.py';assert digest(runner)=='3ce017ec9d6776b1032f2718aa32d26b9318151ec459764dc545c92479ace029'
r=runner.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "matches=[x for x in state['rows'][:-1] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','old_rows':9,'new_rows':8,'runner_sha256':digest(packet/'run.py'),
                  'scope':'conditional signed-gap lift/drop assembly proposal; no Lean result or endpoint'},sort_keys=True,indent=2))
