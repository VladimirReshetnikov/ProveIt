#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'FirstFactor74.lean').read_text()
for x in ('theorem m_at_least_two','theorem first_eval','theorem first_factor_units','(hbeta : (p 0 : DiffRing V)=ι beta)','(hp : Equivalent','(ha : pairResidue a ≠ -1)','(hb\' : pairResidue b ≠ -1)'):
 assert x in s,x
count=0
for beta,J,w,s0 in product(range(1,7),repeat=4):
 q=1+J*beta;X=q*w;Y=q*q*q*s0;m=X*Y*Y
 assert m>=2;count+=1
for X,Y,k,x in product(range(1,6),range(1,5),range(0,5),range(0,5)):
 m=X*Y*Y;ell=(X*Y)*(Y*k)
 assert ell==m*k and x*x-ell*(ell+k)==x*x-(m*k)*(m*k+k)
paths=[P/'FirstFactor74.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean',D/'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean']
print(json.dumps({'scope':'finite arithmetic, source signature and source hashes; no Lean, graph zero or provider proof','size_controls':count,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
