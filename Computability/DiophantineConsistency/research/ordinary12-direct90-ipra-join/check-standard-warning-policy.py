#!/usr/bin/env python3
"""Check baseline acceptance and reject independent retry-log mutations."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;OBS=H/'observations/attempt02';VERIFY=H/'verify-standard-warning.py'
source=json.loads((OBS/'stage-04.json').read_text())['command'][-3];original=(OBS/'stage-04.stdout').read_text()
def call(log,src):return subprocess.run([sys.executable,str(VERIFY),str(log),src],capture_output=True)
rows=[]
with tempfile.TemporaryDirectory(prefix='direct90-warning-mutations-') as td:
 p=Path(td)/'log'
 for name,text,src,expected in [
  ('baseline',original,source,0),
  ('changed_warning',original.replace('Function.update_apply','Function.update_fake',1),source,1),
  ('removed_warning',original.replace('warning:','notice:',1),source,1),
  ('added_warning',original+'warning: extra\n',source,1),
  ('changed_source_path',original,source+'.different',1)]:
  p.write_text(text);r=call(p,src)
  if (r.returncode==0)!=(expected==0):raise RuntimeError('unexpected mutation result '+name)
  rows.append({'case':name,'exit':r.returncode,'stdout_sha256':sha256(r.stdout).hexdigest(),'stderr_sha256':sha256(r.stderr).hexdigest()})
print(json.dumps({'status':'PASS','verifier_sha256':sha256(VERIFY.read_bytes()).hexdigest(),'cases':rows,
 'scope':'warning policy mutation test only; no Lean run'},indent=2))
