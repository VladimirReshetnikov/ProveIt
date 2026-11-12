#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-qcube84-probe/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(840107)
for _ in range(200):
 v={x:rng.randint(1,5) for x in g['witnesses']};p={x:rng.randint(1,5) for x in g['fixed_numerals']};z=calc(v|p)
 q=1+v['J']*p['beta'];X=q*v['w'];Y=q**3*v['s'];k=v['eta']+v['zeta'];ell=X*Y*Y*k;M=q**3*v['J']*p['beta'];P0=ell+k;N=v['r'];rad=1+ell*P0
 assert M>0 and rad>0 and z['A0']==M*M*((P0-N)**2-rad)
s=(P/'FirstNormClient.lean').read_text()
for t in ('fields84 p v hz','old_first_eval','putRoot_self','root_of_scaled_residual','scale_positive','radicand_positive','hport'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for n in ('ordinary14-84-85-zero-fields-draft','ordinary14-direct-first-root-positive-client-draft'):
 p=D/'research'/n;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),n
paths=[P/'FirstNormClient.lean',D/'research/ordinary14-84-85-zero-fields-draft/ZeroFields.lean',D/'research/ordinary14-direct-first-root-graph-client-draft/GraphFirstRootClient.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, finite first-field formula controls and draft receipt replays; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
