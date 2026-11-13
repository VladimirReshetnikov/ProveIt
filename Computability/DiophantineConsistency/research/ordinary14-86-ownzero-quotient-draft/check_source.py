#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'OwnZeroQuotient86.lean').read_text()
for t in ('fields_of_zero p v hz','first_eval p beta v hport','QCubeQuotientFactsDraft.quotient_and_root','(hbeta : 0<beta)','(hJ : 0<v 0)','(hY : 0<v 7)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
count=0
for b in range(1,5):
 Q=(1+b)**3;M=Q*b
 for X in range(1,4):
  for ss in range(1,4):
   Y=Q*ss;k=2;ell=X*Y*Y*k;P0=ell+k;D0=1+ell*P0;tau=2*X*Y*Y+1
   assert tau*tau==D0
   for sign in (-1,1):
    r=P0+ss+sign*tau;z=M*(P0-r)+b*Y
    assert r>0 and z*z==M*M*D0 and abs(z)==M*tau;count+=1
for name in ('ordinary14-86-first-fields-draft','ordinary14-85-86-quotient-facts-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'OwnZeroQuotient86.lean',D/'research/ordinary14-86-first-fields-draft/FirstFields86.lean',D/'research/ordinary14-85-86-quotient-facts-draft/QuotientFacts.lean']
print(json.dumps({'scope':'source inventory, finite first-norm controls and draft receipt replays; no Lean invocation','finite_partial_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
