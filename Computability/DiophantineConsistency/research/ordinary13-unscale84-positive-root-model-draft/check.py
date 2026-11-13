from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-unscale84-positive-root-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks=0
for q in range(1,6):
 for X in range(1,4):
  for s in range(1,4):
   Y=q**3*s;m=X*Y*Y;k=8*m+4;ell=m*k;tau=2*(2*m+1)**2-1
   assert tau*tau==1+ell*(ell+k) and tau>ell+s
   for b in range(1,8):
    for t in range(1,8):
     P=b*t;r=k*(P-1)+t+(tau-(ell+s))
     assert r>0 and b*(ell+k+r+s-k*P)-P==b*tau
     checks+=1
src=(D/'UnscalePositiveRoot.lean.src').read_text()
for t in ['theorem shifted_positive_root','tau-(ell+s)','theorem shifted_root_of_source','root_data b ell k rold P z','theorem shifted_root_of_qcube','qcube_margin q X Y s k tau','(hY : Y=(q*q*q)*s)','(hlarge : 8*X*Y*Y+4≤k)']:
 assert t in src,t
print(json.dumps({'qcube_shifted_root_controls':checks,'actual_graph_binding_proved':False,'lean_executed':False},sort_keys=True,indent=2))
