#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
old=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes());new=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(868701);count=0
while count<300:
 v={x:rng.randint(1,8) for x in new['witnesses']};p={x:rng.randint(0,8) for x in new['fixed_numerals']};q=1+v['J']*p['beta']
 if not v['F']+v['alpha']<q:continue
 z=calc(new,v|p);w={x:v[x] for x in old['witnesses'] if x!='omega'}|p;w['omega']=v['h']+(q-v['F']-v['alpha'])*p['K0'];o=calc(old,w)
 assert w['omega']>(q-v['F']-v['alpha'])*p['K0'] and w['omega']-(q-v['F']-v['alpha'])*p['K0']==v['h'] and all(z[t]==o[t] for t in ('A0','A1','Fa','g72','guard','guarded_out'));count+=1
s=(P/'ConditionalMap87To86.lean').read_text()
for t in ('P72Root.ι_tsub (le_of_lt hstrict)','cast_C beta v hgap','Ring86To87Draft.output_eval','reverse_positive','(P87ShiftedGuard.graph p).output v','C beta v*K<v 13'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-86-to-87-positive-map-draft','ordinary14-86-87-ring-client-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'ConditionalMap87To86.lean',D/'research/ordinary14-86-to-87-positive-map-draft/PositiveMap86To87.lean',D/'research/ordinary14-86-87-ring-client-draft/RingComparison86To87.lean']
print(json.dumps({'scope':'source inventory, finite positive gap/field controls and draft receipt replays; no Lean invocation','finite_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
