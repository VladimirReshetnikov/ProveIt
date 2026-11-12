#!/usr/bin/env python3
"""No-Lean source/graph dependency and exact integer controls."""
from pathlib import Path
import hashlib,json,random,re
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
oldpath=D/'research/ordinary14-qcube84-probe/candidate.json';newpath=D/'research/ordinary14-direct-pell79/candidate.json'
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
old=load(oldpath,'cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61')
new=load(newpath,'5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507')
assert old['witnesses']==new['witnesses'] and old['witnesses'][8]=='r' and old['fixed_numerals']==new['fixed_numerals']
def dep(g):
 d={v:{v} for v in g['witnesses']+g['fixed_numerals']}
 for n,op,a,b in g['source']:d[n]=(d[a] if isinstance(a,str) else set())|(d[b] if isinstance(b,str) else set())
 return d
x,y=dep(old),dep(new)
for n in ('A1','Fa','g72','guard'):assert 'r' not in x[n] and x[n]==y[n]
def calc(g,v):
 v=v.copy()
 for n,op,a,b in g['source']:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v
rng=random.Random(8479)
for _ in range(100):
 v={s:rng.randrange(1,6) for s in old['witnesses']+old['fixed_numerals']};r=rng.randrange(1,8);v['r']=r
 a,b=calc(old,v),calc(new,v);q=1+v['J']*v['beta'];X=q*v['w'];Y=q*q*q*v['s'];k=v['eta']+v['zeta'];ell=(X*Y)*(Y*k);M=q*q*q*v['J']*v['beta'];P=ell+k;D0=1+ell*P
 assert M>0 and D0>0 and a['A0']==M*M*((P-r)**2-D0) and b['A0']==r*r-D0
 assert all(a[n]==b[n] for n in ('A1','Fa','g72','guard'))
 v['r']=r+7;a2,b2=calc(old,v),calc(new,v)
 assert all(a2[n]==a[n] and b2[n]==b[n] for n in ('A1','Fa','g72','guard'))
source=H/'GraphFirstRootClient.lean';s=source.read_text()
for name in ('common_fields','scale_positive','radicand_positive','putRoot_positive','old_first_eval','direct_first_eval','other_fields_ignore_root','positive_first_coordinate_iff'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
paths=[source,D/'research/ordinary14-qcube84-lean-draft/P84QcubeGraph.lean',D/'research/ordinary14-direct-pell79-lean-draft/P79DirectPell.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, dependency and finite controls only; no Lean invocation','controls':100,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
