#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-qcube85-tradeoff/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(850102)
for _ in range(300):
 v={x:rng.randint(0,6) for x in g['witnesses']};p={x:rng.randint(0,6) for x in g['fixed_numerals']};z=calc(v|p)
 q=1+v['J']*p['beta'];X=v['X'];Y=q**3*v['s'];k=v['eta']+v['zeta'];a=X*Y+Y;c=v['eta']+Y*k;delta=3+4*a+a*a;ell=X*Y*Y*k;M=q**3*v['J']*p['beta']
 assert z['A0']==M*M*((ell+k-v['r'])**2-(1+ell*(ell+k)))
 assert z['g72']==(v['i']*c*c)**2-delta*(v['f']**2-1)
s=(P/'DirectNorms85.lean').read_text()
for t in ('def X (v : Fin 14 → V) : V := v 6','fields85 p v hz','first_eval','strong_eval','root_of_scaled_residual','strong_norm_of_ring_residual'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-85-guard-rank-draft','ordinary14-direct-first-root-model-draft','ordinary14-aux-ring-norm-extraction-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'DirectNorms85.lean',D/'research/ordinary14-85-guard-rank-draft/GuardRank85.lean',D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean']
print(json.dumps({'scope':'source inventory, finite 85-field controls and draft receipt replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
