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
rng=random.Random(840114)
for _ in range(300):
 v={x:rng.randint(1,5) for x in g['witnesses']};p={x:rng.randint(0,5) for x in g['fixed_numerals']};q=1+v['J']*p['beta'];v['F']=rng.randint(0,q);z=calc(v|p)
 X=v['X'];Y=q**3*v['s'];a=X*Y+Y;c=v['eta']+Y*(v['eta']+v['zeta']);delta=3+4*a+a*a;R=z['R'];vp=v['f']**2*v['T']*c;vn=v['f']**2*R+c;Q=delta*(v['f']**2-1);u=v['u'];zz=vp-vn
 assert z['Fa']==(zz+u)**2-Q*((zz+u)**2-zz**2)
 assert (z['Fa']==1)==(Q*abs(vp-vn)**2+abs(vp+u-vn)**2==1+Q*abs(vp+u-vn)**2)
s=(P/'AuxNorm85.lean').read_text()
for t in ('fields85 p v hz','GuardRank85Draft.rank_of_85_zero','P72Root.ι_tsub hf2','P72Aux.ι_absdiff_sq','aux_eval p beta v hport','(hv 3)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-85-zero-fields-draft','ordinary14-85-guard-rank-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'AuxNorm85.lean',D/'research/ordinary14-85-guard-rank-draft/GuardRank85.lean',D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean',D/'Lean/DiophantineConsistency/Compact44/P72Aux.lean']
print(json.dumps({'scope':'source inventory, finite literal auxiliary-field controls and draft receipt replays; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
