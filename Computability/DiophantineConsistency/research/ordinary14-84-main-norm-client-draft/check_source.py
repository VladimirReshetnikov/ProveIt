#!/usr/bin/env python3
"""Exact main DAG comparison and finite ring evaluation controls; no Lean."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
new=json.loads((D/'research/ordinary14-qcube84-probe/candidate.json').read_bytes())
old=json.loads((D/'research/ordinary14-direct-pell79/candidate.json').read_bytes())
def shape(g,t):
 rows={a:(op,x,y) for a,op,x,y in g['source']}
 def go(v):
  if v not in rows:return ('leaf',v)
  op,x,y=rows[v]; return (op,go(x),go(y))
 return go(t)
assert new['witnesses']==old['witnesses'] and new['fixed_numerals']==old['fixed_numerals']
assert shape(new,'A1')==shape(old,'A1')
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(840179)
for _ in range(200):
 v={x:rng.randint(1,5) for x in new['witnesses']};p={x:rng.randint(1,5) for x in new['fixed_numerals']};z=calc(new,v|p)
 q=1+v['J']*p['beta'];X=q*v['w'];Y=q**3*v['s'];U=Y*q*q;k=v['eta']+v['zeta'];a=X*Y+Y;c=v['eta']+Y*k;delta=3+4*a+a*a
 main=U*(X+a*c)+(3+4*a)*(U*v['gamma']-(k-z['R']-1))
 assert U>0 and z['A1']==main*main-U*U*(1+delta*c*c)
s=(H/'MainNormClient.lean').read_text()
for t in ('shared_main','natural_main_root'):assert re.search(r'\btheorem\s+'+t+r'\b',s)
for t in ('fields84','main_eval','root_of_scaled_ring_square','hport','hs : 0<v 7') :assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-85-zero-fields-draft','ordinary14-aux-graph-norm-client-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[H/'MainNormClient.lean',D/'research/ordinary14-84-85-zero-fields-draft/ZeroFields.lean',D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean',D/'research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean']
print(json.dumps({'scope':'structural DAG comparison, finite integer controls and draft receipt replay; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
