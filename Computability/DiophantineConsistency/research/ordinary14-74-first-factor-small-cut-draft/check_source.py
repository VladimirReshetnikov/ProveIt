#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
g=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_text())
rows={n:(op,x,y) for n,op,x,y in g['source']}
assert rows['qm']==('*','J','beta') and rows['q']==('+',1,'qm')
assert rows['X']==('*','q','w') and rows['q2']==('*','q','q') and rows['q3']==('*','q','q2') and rows['Y']==('*','q3','s')
assert rows['E']==('*','X','Y') and rows['k']==('+','eta','zeta') and rows['kY']==('*','Y','k') and rows['ell']==('*','E','kY')
assert rows['g30']==('+','ell','k') and rows['g38']==('*','r','r') and rows['g40']==('*','ell','g30') and rows['F0']==('-','g38','g40')
s=(P/'FirstFactorSmallCut74.lean').read_text()
for x in ('theorem first_shape','theorem first_eval_small','(hbeta : (p 0 : DiffRing V)=ι beta)','rw [first_shape]','qExpr p*(qExpr p*qExpr p)'):
 assert x in s,x
assert 'simp [P74PositiveGuard.graph' not in s
controls=0
for beta,J,w,s0,r,eta,zeta in product(range(-1,3),repeat=7):
 q=1+J*beta;X=q*w;Y=q*(q*q)*s0;k=eta+zeta;ell=(X*Y)*(Y*k);m=X*Y*Y
 assert r*r-ell*(ell+k)==r*r-(m*k)*(m*k+k);controls+=1
paths=[P/'FirstFactorSmallCut74.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean',D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean',D/'research/ordinary14-positive-guard74/candidate.json']
print(json.dumps({'scope':'literal row and finite algebra controls; no Lean, provider or resource result','signed_controls':controls,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
