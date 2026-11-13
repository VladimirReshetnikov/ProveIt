from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-unscale84-first-margin-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-unscale84-first-margin-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
checks=0
for ell in range(50):
 for s in range(ell+1):
  for k in range(3*s,3*s+15):
   d=1+ell*(ell+k)-(ell+s)**2
   assert d==1+ell*(k-3*s)+s*(ell-s) and d>=1
   t=isqrt(1+ell*(ell+k))
   if t*t==1+ell*(ell+k):assert ell+s<t
   checks+=1
special=0
for q in range(1,6):
 for X in range(1,5):
  for s in range(1,5):
   Y=q**3*s;m=X*Y*Y;k=8*m+4
   assert s<=Y<=m and 3*s<=k and s<=m*k
   tau=2*(2*m+1)**2-1
   assert tau*tau==1+m*(m+1)*k*k and m*k+s<tau
   special+=1
src=(A/'UnscaleFirstMargin.lean.src').read_text()
for term in ['(hnorm : tau*tau=1+ell*(ell+k)) (hk : 3*s≤k) (hs : s≤ell)',
 '(hs : s≤m)','(hk : 8*m+4≤k)','(hq : 1≤q) (hX : 1≤X) (hs : 0<s)',
 '(hY : Y=(q*q*q)*s)','exact margin_of_first_norm']:
 assert term in src,term
parent=Path('Lean/DiophantineConsistency/Compact44/P73Converse.lean').read_text()
assert 'private theorem tau_gt' in parent and '(hk : 3 * s ≤ k) (hs : s ≤ ell) (hs0 : 0 ≤ s)' in parent
print(json.dumps({'author_receipt_reproduces':True,'general_gap_controls':checks,'qcube_norm_controls':special,'lean_executed':False,'graph_binding_proved':False},sort_keys=True,indent=2))
