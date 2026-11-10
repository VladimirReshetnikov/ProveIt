#!/usr/bin/env python3
"""Review symbolic forward/reverse assembly source and guarded preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign24-zero-assembly-check'
draft = research / 'nine-sharing-sign24-zero-assembly-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign24ForwardBridge', 'Sign24ReverseBridge']
rows = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
content = []
for name, row in zip(names, rows):
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M) == row['imports']
    content.append(source.read_text())
assert rows[0]['imports'] == ['DiophantineConsistency.Sign24Transfers00','DiophantineConsistency.Sign24Transfers01','DiophantineConsistency.Sign24Transfers02']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign24ForwardBridge']
gates = ['Y','E','kY','Delta','main_root','Dc2','tau','N0','Nt','cTminusR','V','normalized_S','V2minusY2','Na','scaled_Ns']
fwd, rev = content
old_rows = fwd.split('theorem old_rows ',1)[1].split(':= by rfl',1)[0]
new_rows = rev.split('theorem new_rows ',1)[1].split(':= by rfl',1)[0]
assert re.findall(r'Sign24Transfers.old(\w+) p', old_rows) == gates
assert re.findall(r'Sign24Transfers.new(\w+) p', new_rows) == gates
assert fwd.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 1
assert rev.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 1
assert 'Sign24Coordinate.q3_zero p beta v hp0' in fwd
assert 'Sign24Coordinate.lift_drop p beta v hp0 hz' in rev
for gate in gates:
    assert f'Sign24Transfers.{gate}_eval p beta v hp0)).mpr' in fwd
    assert f'Sign24Transfers.{gate}_eval p beta (Sign24Coordinate.drop v) hp0)).mp' in rev
assert 'SharingSign24Squares.seed_zero_iff_residuals' in fwd and 'SharingSign25Squares.seed_zero_iff_residuals' in rev
upstream = root / 'reviews/nine-sharing-sign24-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet / 'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH', 'old_rows':16, 'new_rows':15, 'runner_sha256':digest(packet / 'run.py'),
                  'scope':'symbolic beta-cast assembly proposal; no Lean result or current-port endpoint'},sort_keys=True,indent=2))
