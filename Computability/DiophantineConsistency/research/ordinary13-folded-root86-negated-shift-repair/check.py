#!/usr/bin/env python3
"""Finite exact checks of scalar shift/gcd criterion; no Lean."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
p=D/'research/ordinary13-folded-root86-negated/candidate.json'; raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166';g=json.loads(raw);rows={r[0]:r for r in g['source']}
for n,row in {'qF':['qF','-','q','F'],'C':['C','-','qF','alpha'],'g44':['g44','*','qF','qm'],'G':['G','+','alpha','g44'],'Bt':['Bt','-','g27','g28']}.items():assert rows[n]==row
controls=success=fail=0
for b in range(1,10):
 q=b+1
 for X in range(1,8):
  for K in range(0,4):
   B=X+K*q+1; A=q*B; L=b//math.gcd(b,B)
   for F in range(1,8):
    for alpha in range(1,20):
     C=q-F-alpha;Bt=C*(X+K*q)-F*q
     if Bt>0 or Bt%b:continue
     D0=min(F-1,(alpha-1)//b);delta0=L*((1-Bt+A*L-1)//(A*L)); brute=[]
     G=b*(q-F)+alpha
     for d in range(D0+1):
      F1=F-d;alpha1=alpha-b*d;C1=q-F1-alpha1;Bt1=C1*(X+K*q)-F1*q
      assert b*(q-F1)+alpha1==G and C1==C+q*d and Bt1==Bt+A*d
      assert (Bt1%b==0)==(d%L==0)
      if Bt1>0 and Bt1%b==0:brute.append(d)
     assert bool(brute)==(delta0<=D0)
     if brute:assert min(brute)==delta0;success+=1
     else:fail+=1
     controls+=1
assert controls>100 and success>0 and fail>0
print(json.dumps({'controls':controls,'repairable':success,'unrepairable_in_restricted_family':fail,'scope':'conditional scalar shift criterion; finite failures need not be graph zeros; no Lean'},sort_keys=True,indent=2))
