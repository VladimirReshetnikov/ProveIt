#!/usr/bin/env python3
"""Independent 87 first-Pell index source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-first-index-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','dd8b018b09f6be2201dd1d4a32b64fc740b6f5426167f81862a9d620bc16f8b8')
s=pin(A/'FirstIndex87.lean','687d4aa130cc4adcb36046ceb22ef52ae7ec57b97814abf5c58f916db7206183').decode()
pin(A/'check_source.py','aaf0149dc9b6d8a67aef66c89566f6fd57f1f8ff5eb6608c7a6377727a04b6d5')
receipt=pin(A/'observation.json','469ee6222d045dd9092844347e03b3cfaf1ce4800b6ed3aa2d5c7df6fcee21d2')
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'FirstQuotient87Draft.quotient_and_root p beta v hbeta hJ hY hport hz',
 'have he : m-1+1=m := tsub_add_cancel_of_le hm1',
 'ArithmeticPellFirstNorm.solution_residues (m-1) tau (k v) hdisc',
 'tau=1+2*m*r','k v=2*n+4*m*w'):
 assert f in s,f
n=0
for m in range(1,11):
 p=2*m+1;discriminant=p*p-1;x,y=1,0
 for index in range(1,12):
  x,y=p*x+discriminant*y,x+p*y
  k=2*y
  assert x*x==1+m*(m+1)*k*k
  assert (x-1)%(2*m)==0 and (k-2*index)%(4*m)==0;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-87-first-quotient-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero first index source review; no Lean or rank identification','finite_pell_cases':n},sort_keys=True,indent=2))
