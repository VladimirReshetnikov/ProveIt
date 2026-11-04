#!/usr/bin/env python3
"""Exercise copied supervisor with altered runner and controlled stub results; no Lean."""
from pathlib import Path
from hashlib import sha256
import json, subprocess, sys, tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
OUTER=H/'run-outer.py'
EXPECTED='fa721123aa8ec78ea7339978ca569ba798450a6c10a91421fe18080ee2a23abf'
O=H/'observations/outer-policy-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
if O.exists() or sha(OUTER)!=EXPECTED:raise SystemExit('output exists or wrapper drift')
checks={}
with tempfile.TemporaryDirectory(prefix='trace74-parametric-outer-control-') as td:
 root=Path(td); (root/'observations/preflight-attempt01').mkdir(parents=True); (root/'observations/policy-attempt01').mkdir(parents=True)
 pre=root/'observations/preflight-attempt01/terminal.json';pol=root/'observations/policy-attempt01/result.json'
 pre.write_text('{}\n');pol.write_text('{}\n')
 outer=OUTER.read_text().replace('7e1e902c328fe6604180468ec78991ca45831ae3a16bfbac2d968c649e4a9d95',sha(pre)).replace('80a1c6d7c6fbd24845f5ca9fcbb2e79ba3f07ee8852296001a69bf4e8d9607a3',sha(pol))
 stub="""from pathlib import Path\nimport json,sys\nH=Path(__file__).resolve().parent\na=sys.argv[sys.argv.index('--attempt')+1]\no=H/'observations'/a\no.mkdir(parents=True)\nmode=(H/'mode').read_text()\nif mode=='bad': (o/'result.json').write_text('{')\nif mode=='failed': (o/'result.json').write_text(json.dumps({'status':'FAILED'}))\nif mode=='pass': (o/'result.json').write_text(json.dumps({'status':'PASS'}))\n"""
 run=root/'run.py';run.write_text(stub)
 outer=outer.replace('39aefdea2a7d029474ccf0bf5df0b228f02ad75d2c5dead561b926c8c1b5a5e1',sha(run))
 wr=root/'run-outer.py';wr.write_text(outer)
 def invoke(attempt):return subprocess.run([sys.executable,'-I','-S','-B',str(wr),'--attempt',attempt],capture_output=True,text=True)
 run.write_text(stub+'# drift\n');p=invoke('attempt01');checks['altered_runner_rejected_before_child']=p.returncode!=0 and not (root/'observations/outer-attempt01').exists()
 run.write_text(stub)
 for n,mode in enumerate(('missing','bad','failed','pass'),2):
  (root/'mode').write_text(mode);attempt=f'attempt{n:02d}';p=invoke(attempt)
  terminal=json.loads((root/'observations'/('outer-'+attempt)/'terminal.json').read_text())
  checks[f'{mode}_child_status']=(p.returncode==0)==(mode=='pass') and terminal['exit']==0 and terminal['child_status']==({'failed':'FAILED','pass':'PASS'}.get(mode))
 p=invoke('attempt05');checks['existing_attempt_rejected']=p.returncode!=0
if sha(OUTER)!=EXPECTED or not all(checks.values()):raise SystemExit('wrapper drift or failed control: '+repr(checks))
O.mkdir(parents=True)
r={'status':'PASS','outer_sha256':EXPECTED,'test_sha256':sha(__file__),'checks':checks,'scope':'copied supervisor and controlled Python stubs; no Lean'}
(O/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'sha256':sha(O/'result.json')}))
