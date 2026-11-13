from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-zero-norm-large-k-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
k2=0
for X in range(0,100):
 for Y in range(1,100):
  A=X*Y+Y+2;c=2+2*Y;delta=A*A-1;assert 1<c<2*A
  n=1+delta*c*c;d=isqrt(n);assert d*d<n
  k2+=1
pell=0
for m in range(1,40):
 for k in range(3,1800):
  n=1+m*(m+1)*k*k;t=isqrt(n)
  if t*t==n:assert 8*m+4<=k;pell+=1
assert pell>0
src=(D/'ZetaZeroNormLargeK.lean.src').read_text()
for x in ['theorem two_ordinate_impossible','(hmain : d*d=1+Delta*(k+Y*k)*(k+Y*k))','apply no_main_square A c Delta d','theorem large_first_ordinate','(hk : 0<k)','two_le_ordinate','first_ordinate_large']:
 assert x in src,x
print(json.dumps({'k2_main_square_exclusions_checked':k2,'first_pell_solutions_checked':pell,'graph_zero_binding_proved':False,'lean_executed':False},sort_keys=True,indent=2))
