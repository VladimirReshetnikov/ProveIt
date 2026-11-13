#!/usr/bin/env python3
"""Finite controls and syntactic bounds; not an all-model proof."""
import hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;old=json.loads((P.parent/'nine-sharing-sign28-sextic-candidate/seed.json').read_text());new=json.loads((P/'seed.json').read_text())
def degree(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 a,b=degree(t[1]),degree(t[2]);return a+b if t[0]=='mul' else max(a,b)
def ev(t,v,p):
 if t[0]=='var':return v[t[1]]
 if t[0]=='num':return t[1]
 if t[0]=='port':return p[t[1]]
 a,b=ev(t[1],v,p),ev(t[2],v,p);return {'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[t[0]]()
def lift(v):
 u=v[21];return v[:21]+[u+1,u*(u+2)]+v[22:]
def drop(v):
 assert v[21]>=1 and v[22]==(v[21]-1)*(v[21]+1)
 return v[:21]+[v[21]-1]+v[23:]
rng=random.Random(27021);p={'beta':3,'K0':7,'MC':5,'MF':9};controls=16
for _ in range(controls):
 v=[rng.randrange(4) for _ in range(28)];w=lift(v);assert len(w)==29 and drop(w)==v
 before=[(r['gate'],ev(r['expr'],w,p)) for r in old['residuals']];after=[(r['gate'],ev(r['expr'],v,p)) for r in new['residuals']];assert dict(before)['N1']==0 and [(k,z) for k,z in before if k!='N1']==after
assert new['witness_count']==27 and len(new['residuals'])==18 and max(degree(r['expr']) for r in new['residuals'])==3 and old['residuals'][0]==new['residuals'][0]
print(json.dumps({'status':'PASS_FINITE_CONTROLS_AND_SYNTACTIC_BOUND','seed_sha256':hashlib.sha256((P/'seed.json').read_bytes()).hexdigest(),'witnesses':27,'residuals':18,'max_residual_syntactic_degree':3,'finite_lift_drop_controls':controls,'scope':'finite integer controls and syntactic bounds only; no all-model bridge or Lean proof'},indent=2,sort_keys=True))
