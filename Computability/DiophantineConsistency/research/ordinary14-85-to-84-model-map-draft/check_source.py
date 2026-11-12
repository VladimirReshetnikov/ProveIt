#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'ModelMap85To84.lean').read_text()
for t in ('PowerRecovery85Draft.power','Divides3X85Draft.divides_three_X','mersenne_divides_X','map_85_to_84','(hbeta46 : 46≤beta)','(ht : 4≤t)','(hradix : beta=Exp.exp t-1)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0;implications=0
for t in range(4,10):
 beta=2**t-1
 for J in range(1,41):
  q=1+J*beta
  for R in range(15):
   X=2**R;count+=1
   if 3*X%q==0: assert X%q==0;implications+=1
assert 3*(2**4)%3==0 and (2**4)%3!=0
for name in ('ordinary14-85-power-recovery-draft','ordinary14-85-divides-3x-draft','ordinary14-84-85-conditional-model-draft','ordinary14-modified-carrier-model-facts-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'ModelMap85To84.lean',D/'research/ordinary14-85-power-recovery-draft/PowerRecovery85.lean',D/'research/ordinary14-85-divides-3x-draft/Divides3X85.lean',D/'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean']
print(json.dumps({'scope':'source inventory, finite Mersenne controls and four draft receipt replays; no Lean invocation','finite_controls':count,'cases_with_q_dividing_three_X':implications,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
