#!/usr/bin/env python3
"""Check the exact warning policy and v9 inputs without invoking Lean."""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-direct90-ipra-join';O=H/'observations/attempt02'
S=H/'run-v9.py';V=H/'verify-standard-warning.py';E=H/'expected-standard-warning.txt';R=H/'observations/attempt02-rejected-object'
PINS={S:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03',
 V:'225e368ddc1350f4db7a03fd5ce84693b7a53a0d89330ef0e338c8b9e12e4a93',
 E:'97d21d17b2e82cd1f87c74a35b3bb9e8fd98d610e6cb33b7f8e1cf1faab59006',
 O/'result.json':'69d3eecfbf7647e83fbfe100968d270fe5ce72aa6aaaf0525d6e041f2c3bffab',
 O/'stage-04.json':'a6c83a28ff10a68f8109a7d2ffd6628dcf14860785b8df38e3589b5d1cf24d9a',
 O/'stage-04.stdout':'f5818e501c68cad86a28a22ddd349e1e0880d37e22c1decb1580bf71cdc7e9f8',
 R/'receipt.json':'028331f3870a81502c1c88ad575c2f3fe6a1634006e7bf569b0ffd6f301d69c5',
 R/'IPRAStandardTheory.olean':'47d2fb646cdb4b07afd68a4d97d9f3d04ba0453dff295d61632d131f5408efbf'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'pin drift '+str(p))
result=json.loads((O/'result.json').read_text());process=json.loads((O/'stage-04.json').read_text());text=(O/'stage-04.stdout').read_text()
need(result['status']=='FAILED' and len(result['stages'])==3 and 'stage diagnostics' in result['error'],'retained rejected attempt')
need(process['exit']==0 and process['reason'] is None and not (O/'stage-04.stderr').read_bytes(),'stage process receipt')
need(process['stdout_sha256']==PINS[O/'stage-04.stdout'] and text.count('warning:')==3,'warning count')
receipt=json.loads((R/'receipt.json').read_text());need(receipt['sha256']==PINS[R/'IPRAStandardTheory.olean'] and receipt['bytes']==(R/'IPRAStandardTheory.olean').stat().st_size,'rejected object')
source=process['command'][-3];tests={'baseline':text,'column':text.replace(':92:42:',':92:43:',1),
 'simp_argument':text.replace('Function.update_of_ne hj','Function.update_of_ne hz',1),
 'extra_warning':text+'warning: extra\n','tagged_warning':text+'warning(lean.example): extra\n',
 'extra_error':text+'error(lean.example): extra\n','sorryAx':text+'sorryAx\n',
 'missing_line':text.replace('Hint: Omit it from the simp argument list.\n','',1),
 'wrong_source':text.replace(source,'/tmp/other/source.lean',1),'empty':''}
outcomes={}
with tempfile.TemporaryDirectory(prefix='direct90-warning-independent-') as tmp:
 for name,content in tests.items():
  p=Path(tmp)/name;p.write_text(content)
  r=subprocess.run([sys.executable,'-I','-S','-B',str(V),str(p),source],capture_output=True,timeout=30)
  accepted=r.returncode==0;need(accepted==(name=='baseline'),'mutation outcome '+name)
  if accepted:need(not r.stderr,'baseline verifier stderr')
  outcomes[name]='accepted' if accepted else 'rejected'
spec=importlib.util.spec_from_file_location('v9_warning_review',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for level in ('warning','error'):
 need(m.diagnostic(level+': test',level) and m.diagnostic(level+'(lean.example): test',level) and not m.diagnostic('ordinary text',level),'coded diagnostic matcher')
for p,h in m.PINS.items():need(sha(p)==h,'runner input drift '+str(p))
final=json.loads(m.FINAL.read_text());m.validate_final(final);m.manifest_recheck(final)
producers=m.producer_receipts(json.loads(m.APPROVED_CONE.read_text()),final);need(len(producers)==425,'producer count')
for p,h in PINS.items():need(sha(p)==h,'pin changed '+str(p))
print(json.dumps({'status':'PASS','v9_sha256':PINS[S],'warning_cases':outcomes,'producer_modules':len(producers),
 'scope':'external warning policy, mutation and provider preflight; no Lean replay or join'},indent=2,sort_keys=True))
