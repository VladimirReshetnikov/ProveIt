#!/usr/bin/env python3
"""Finite source and algebra controls for an ordinary V-positivity lemma."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);r={x[0]:x for x in g['source']}
for name,row in {'q':['q','+','qm',1],'X':['X','*','w','q'],'Y':['Y','*','s','q3'],'E':['E','*','X','Y'],'k':['k','+','eta','zeta'],'c':['c','+','kY','eta'],'tau':['tau','-','tau_partial','R'],'V':['V','-','f2inner','c'],'Nt':['Nt','-','transport_partial','zqm']}.items():assert r[name]==row
for q in range(2,200):
 assert (q*q-q-1)*(q*q-1)+(2*q+1)*(q-1)==q**4-q**3
 for u in range(2,q):
  for alpha in (1,u-1):
   gap=(q-1)*u+alpha
   assert 2*q-1<=gap<=q*q-q-1
# At R=1 the first Pell index really can be 1: 1<R is essential.
E,Y,R,n=32,8,1,16;m=E*Y;k=2;tau=2*m+1
assert tau==E*n+k-R and tau*tau-m*(m+1)*k*k==1
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'rank_polynomial_identity_controls':198,'boundary_control':{'E':E,'Y':Y,'R':R,'n':n,'k':k},'scope':'finite graph and arithmetic controls; unbounded proof is ordinary mathematics, not Lean'},sort_keys=True,indent=2))
