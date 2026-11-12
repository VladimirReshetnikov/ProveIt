#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'PowerRecovery85.lean').read_text()
for t in ('P72ExactIndices85Draft.exact_indices','Growth85Draft.growth','projection_quotient aa R','mod_cancel hHp hres','(hbeta46 : 46≤beta)','X v=Exp.exp (naturalRank beta MC MF v)'):assert t in s
assert 'FreeJPowerFinish.graph_power' not in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0;nondiv=0
for q in range(2,10):
 for X in range(1,13):
  if 3*X%q:continue
  for ss in range(1,4):
   Y=q**3*ss;a=Y*(X+1);H=3+4*a;c=7;dd=4*q*q*ss*(X+1);M=X+a*c+H*X//q;W=0;gamma=0
   assert H==3+q*dd and q*M==q*(X+a*c)+H*X
   left=H*(M+H*W)+3*(X+a*c+H*gamma)
   right=3*(M+H*W)+H*(X+a*c+H*gamma)+H*dd*X
   assert left==right
   if X%q:nondiv+=1
   count+=1
assert nondiv>0
for H in range(4,70):
 for X in range(H//3+1):
  for E in range(H//3+1):
   if 3*X<H and 3*E<H and (3*X)%H==(3*E)%H:assert X==E
p=D/'research/ordinary14-85-growth-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'PowerRecovery85.lean',p/'Growth85.lean',D/'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean',D/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean']
print(json.dumps({'scope':'source interface, finite algebra/remainder controls and draft receipt replay; no Lean invocation','cross_balance_controls':count,'controls_q_not_dividing_X':nondiv,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
