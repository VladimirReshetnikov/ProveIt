#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'OwnZeroGuardStrict74.lean').read_text()
for t in ('(hd : Discrete (DiffRing V))','(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)','guard_factor_one p beta v hbeta hb','shifted_guard_gt_one hd','(hz : InternalZero (P74PositiveGuard.graph p).output v)'):
 assert t in s,t
rng=random.Random(747478);n=0
for _ in range(3000):
 J,beta,w,F,alpha,K,h=[rng.randrange(1,8) for _ in range(7)];q=1+J*beta;X=q*w;b=J*beta;C=q-F-alpha
 guard=C*(X+K)+(q-F)-b*h
 if guard==1:
  assert C*(X+K)-F==b*(h-1)
  assert q<=X and h>1;n+=1
assert n>0
paths=[P/'OwnZeroGuardStrict74.lean',D/'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean',D/'research/ordinary14-positive-guard74-model-fact-draft/Guard74Strict.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean']
print(json.dumps({'scope':'conditional source and finite scalar controls; no Lean or graph zero','guard_cases':n,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
