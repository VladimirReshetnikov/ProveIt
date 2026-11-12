from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive83-reverse-arithmetic-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-positive83-reverse-root-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
gaps=pos=div=0;signs=set()
for q in range(1,14):
 for F in range(0,9):
  for alpha in range(0,9):
   C=q-F-alpha
   for K in range(6):
    for X in range(0,25):
     Q=C*(X+K*q)-F*q;P=C*(X+K)-F
     assert Q-P==(q-1)*(C*K-F)
     if Q>0:
      assert C>0;gaps+=1
      if X>0:
       assert P>0;pos+=1; signs.add((C*K-F>0)-(C*K-F<0))
      if q>1 and Q%(q-1)==0:
       assert P%(q-1)==0;div+=1
assert min(gaps,pos,div)>0 and signs=={-1,0,1}
roots=0
for ell in range(18):
 for k in range(2,20):
  t=isqrt(1+ell*(ell+k))
  if t*t!=1+ell*(ell+k): continue
  for b in range(1,9):
   for u in range(1,8):
    P=b*u;r=k*(P-1)+u+t-ell
    assert r>0 and b*(ell+k+r-k*P)-P==b*t
    roots+=1
src=(A/'Positive83ReverseRoot.lean.src').read_text()
for x in ['theorem first83','theorem first81_update','theorem gap_of_carrier','mul_nonpos_of_nonpos_of_nonneg hc hA','PositiveCarrierDataDraft.root_data','PositiveCarrierDataDraft.P_positive','P72Root.ι_tsub (le_of_lt hgap)','CompanionCarrierFactsDraft.reduced_companion','CompanionCarrierFactsDraft.positive_target']:
 assert x in src,x
print(json.dumps({'author_receipt_reproduces':True,'positive_Q_gap_cases':gaps,'positive_Q_P_cases':pos,'reverse_divisibility_cases':div,'positive_root_cases':roots,'negative_zero_positive_D_seen':True,'lean_executed':False},sort_keys=True,indent=2))
