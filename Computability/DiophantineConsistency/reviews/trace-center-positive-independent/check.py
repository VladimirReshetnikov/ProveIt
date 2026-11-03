from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-trace-center-positive');o=root/'observations/attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='1b9f0e79fdf2697af9f07f32fe4ed918c3522d768585c2eedcfa465905067fed';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='c1502792816d437971e4fa1fc632a3d78fbaafe89a15925820b11a136c29799e'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().splitlines()==["'TraceCenterPositive.square_term_lt_n' depends on axioms: [propext, Classical.choice, Quot.sound]","'TraceCenterPositive.center_positive' depends on axioms: [propext, Classical.choice, Quot.sound]"] and not (o/'stderr').read_text()
code=(root/'TraceCenterPositiveV2.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring'] and not re.search(r'\b(sorry|admit)\b',code);s=re.sub(r'\s+','',code)
for x in ['(htau:0<tau)','(hy:0<y)','(hf:kappa<f)','(hbalance:n+kappa=tau*f*y+u*u*(b*t)+t+rho)']:assert s.count(x)==2,x
assert 'u*u*(b*t)<n:=by' in s and '0<n-u*u*(b*t):=' in s
for n in ['Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring']:
 p=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')/(n.replace('.','/')+'.olean');assert str(p) in r['pins'] and sha(p)==r['pins'][str(p)]['sha256']
a=root/'observations/attempt01';f=json.loads((a/'terminal.json').read_text());assert f['status']=='FAILED' and sha(a/'stdout')==f['stdout_sha256'] and 'error' in (a/'stdout').read_text()
print('PASS: exact model balance, strict tau/y/kappa hypotheses, strict square bound and positive truncated center, direct inputs and failed attempt verified; no graph binding.')
