from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-qcube-main-index-boundary')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-first-main-index-boundary')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
p=Path('research/ordinary13-free-aux-square-two-norm-positive-k-transfer')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Coefficients of 4q³−7q²−14q+14 after q=8+t.
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def sc(a,n):return [n*x for x in a]
q=[8,1];q2=mul(q,q);q3=mul(q2,q)
poly=add(add(sc(q3,4),sc(q2,-7)),add(sc(q,-14),[14]))
assert poly[0]>0 and all(x>=0 for x in poly)
# Finite scalar checks of the sharpened exponent consequence and rank gap;
# these do not materialize fixed-compact q or Pell iterates.
controls=0
for q0 in (8,16,32,64):
 lower=(2*q0-1)*(q0*q0-1)+1
 assert 7*lower>10*q0**3
 for m in range(1,500):
  for n in range(1,m+1):
   if 7*(n-1)+3<5*(m-1):
    assert 7*n+1<5*m
    if m<=q0**3:assert 2*n<lower
    controls+=1
print(json.dumps({'predecessor_receipt_reproduced':True,'q_ge_8_rank_gap_polynomial_positive':True,'finite_exponent_controls':controls,'positive_m_at_most_q_cubed_excluded_in_inherited_slice':True,'m_zero_excluded_conditionally_by_two_norm_transfer':True,'other_slices_open':True,'lean_executed':False},sort_keys=True,indent=2))
