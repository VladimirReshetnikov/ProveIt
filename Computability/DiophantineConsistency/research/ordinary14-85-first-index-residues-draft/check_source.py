#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'FirstIndexResidues85.lean').read_text()
for t in ('positive','solution_residues (Q-1) tau K hdisc','tsub_add_cancel_of_le hQ1','tau=1+2*Q*r','K=2*n+4*Q*s'):
 if t=='positive': continue
 assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0
for Q in range(1,13):
 b=2*(Q-1)+1;delta=(b+1)*(b+3);x,y=1,0
 for n in range(5):
  K=2*y;assert x*x==1+Q*(Q+1)*K*K
  assert (x-1)%(2*Q)==0 and (K-2*n)%(4*Q)==0
  assert x==1+2*Q*((x-1)//(2*Q)) and K==2*n+4*Q*((K-2*n)//(4*Q))
  x,y=(b+2)*x+delta*y,x+(b+2)*y;count+=1
p=D/'research/ordinary14-85-direct-norms-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'FirstIndexResidues85.lean',p/'DirectNorms85.lean',D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean']
print(json.dumps({'scope':'source inventory, finite recurrence/residue controls and draft receipt replay; no Lean invocation','finite_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
