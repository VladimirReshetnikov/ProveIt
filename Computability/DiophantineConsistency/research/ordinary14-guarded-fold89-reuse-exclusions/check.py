#!/usr/bin/env python3
"""Finite scalar controls for four proposed existing-input guard substitutions."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
p=D/'research/ordinary14-guarded-fold89-26/candidate.json'; raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='4f0758dd44c61c72c7ac19b244336306bcb588f600debe6b4dbdb686916a6012'
g=json.loads(raw); rows={r[0]:r for r in g['source']};assert rows['guard']==['guard','-','Bt','h']
count=0
for b in range(1,16):
 q=b+1
 for K in range(q*q):
  for X in range(1,8):
   for F in range(1,b+1):
    for alpha in range(1,b+1):
     C=q-F-alpha;Bt=C*(X+K*q)-F*q
     if Bt<=0 or Bt%b:continue
     assert 1<=F<b and 1<=alpha<b
     assert Bt!=F and Bt!=alpha
     t=Bt//b; Y=q**3; k=8*X*Y*Y+4
     assert 4*Bt<k and 2*(Bt+t)<k
     count+=1
assert count>100
for beta in range(2,16):
 for J in range(1,50):assert J%(J*beta)!=0
print(json.dumps({'finite_scalar_controls':count,'finite_J_controls':14*49,'scope':'four individual guard reuses fail under stated hypotheses; no Lean or universal guard impossibility'},sort_keys=True,indent=2))
