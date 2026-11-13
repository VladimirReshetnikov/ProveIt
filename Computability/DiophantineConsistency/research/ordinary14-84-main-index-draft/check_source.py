#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'MainIndex.lean').read_text()
for t in ('PositiveMainBalance84Draft.norm_and_balance','ArithmeticPellClassification.solution_index a d c hnorm','m≤c ∧ xcoord m a=d ∧ ycoord m a=c','hbeta hport hK hMC hMF hv hz'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for a in range(50):
 delta=(a+1)*(a+3);assert delta==3+4*a+a*a
 d=a+2;c=1;assert d*d==1+delta*c*c
p=D/'research/ordinary14-84-positive-main-balance-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'MainIndex.lean',p/'PositiveMainBalance.lean',D/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean',D/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean']
print(json.dumps({'scope':'source inventory, finite delta/first-step controls and draft receipt replay; no Lean invocation','finite_controls':50,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
