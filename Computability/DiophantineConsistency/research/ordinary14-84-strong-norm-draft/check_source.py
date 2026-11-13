#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
new=json.loads((D/'research/ordinary14-qcube84-probe/candidate.json').read_bytes());old=json.loads((D/'research/ordinary14-direct-pell79/candidate.json').read_bytes())
def shape(g,t):
 rows={a:(op,x,y) for a,op,x,y in g['source']}
 def go(v):
  if v not in rows:return ('leaf',v)
  op,x,y=rows[v];return (op,go(x),go(y))
 return go(t)
assert new['witnesses']==old['witnesses'] and new['fixed_numerals']==old['fixed_numerals'] and shape(new,'g72')==shape(old,'g72')
def calc(v):
 v=v.copy()
 for name,op,x,y in new['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(840109)
for _ in range(200):
 v={x:rng.randint(0,5) for x in new['witnesses']};p={x:rng.randint(0,5) for x in new['fixed_numerals']};z=calc(v|p)
 q=1+v['J']*p['beta'];X=q*v['w'];Y=q**3*v['s'];a=X*Y+Y;k=v['eta']+v['zeta'];c=v['eta']+Y*k;delta=3+4*a+a*a
 assert z['g72']==(v['i']*c*c)**2-delta*(v['f']*v['f']-1)
s=(P/'StrongNorm.lean').read_text()
for t in ('fields84 p v hz','shared_strong p','strong_eval p beta v hport','strong_norm_of_ring_residual'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for n in ('ordinary14-84-85-zero-fields-draft','ordinary14-aux-graph-norm-client-draft'):
 p=D/'research'/n;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),n
paths=[P/'StrongNorm.lean',D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean',D/'research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean']
print(json.dumps({'scope':'source inventory, shared DAG, finite strong-field controls and draft receipt replay; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
