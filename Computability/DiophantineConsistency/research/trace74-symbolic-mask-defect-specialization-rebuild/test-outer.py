#!/usr/bin/env python3
"""Exercise copied supervisor with altered runner and controlled stub results; no Lean."""
from pathlib import Path
from hashlib import sha256
import json, subprocess, sys, tempfile
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
OUTER=H/'run-outer.py'
EXPECTED='4e55ecfbfba6d8f1b44dca20a603f7a526021d398d19bd43c10a8e6faf34a376'
O=H/'observations/outer-policy-attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
if O.exists() or sha(OUTER)!=EXPECTED:raise SystemExit('output exists or wrapper drift')
checks={}
with tempfile.TemporaryDirectory(prefix='trace74-parametric-outer-control-') as td:
 root=Path(td); (root/'observations/preflight-attempt02').mkdir(parents=True); (root/'observations/policy-attempt02').mkdir(parents=True)
 pre=root/'observations/preflight-attempt02/terminal.json';pol=root/'observations/policy-attempt02/result.json'
 pre.write_text('{}\n');pol.write_text('{}\n')
 outer=OUTER.read_text().replace('ea9ffc4ba077f878041426df61a0b42e8ac34c340c1fbc54de2eeae9556b306d',sha(pre)).replace('077c2d8b10947ab5483d7a27a56240cb98e0e85a21f862da441eeccbf95df15f',sha(pol))
 stub="""from pathlib import Path\nimport json,sys\nH=Path(__file__).resolve().parent\na=sys.argv[sys.argv.index('--attempt')+1]\no=H/'observations'/a\no.mkdir(parents=True)\nmode=(H/'mode').read_text()\nif mode=='bad': (o/'result.json').write_text('{')\nif mode=='failed': (o/'result.json').write_text(json.dumps({'status':'FAILED'}))\nif mode=='pass': (o/'result.json').write_text(json.dumps({'status':'PASS'}))\n"""
 run=root/'run.py';run.write_text(stub)
 outer=outer.replace('8dacb1812a1fe35bdca6a88abd3a9692d0c7af7cf66179e4c5e72b7762fa201f',sha(run))
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
