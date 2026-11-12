#!/usr/bin/env python3
"""Independent first/main large-k source review; no Lean."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-first-main-large-k-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstMainLargeK.lean','65d2de66fec31d7cc2d79687acc353638e864077c561af12829d93007d430e61').decode()
pin(A/'check_source.py','cac79aabbb1ce32ad99945b9b16891790100dbc3477ee1f77cdcccda9c0fbe21')
receipt=pin(A/'observation.json','a03895fbbab8a6749857459f73d6436dc12e3b8d03ff0583e8a9090abb2d5f94')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-first-main-large-k-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='6a0b9791ab4e03de7414a3b1d1399039f731bc189bcf4fb36652c17f890f0cbd'
for name,ch,rh in (
 ('ordinary14-model-main-square-gap-draft-independent','268fbdfe448cee66e7f87c6c49efb04ac93ffb1053422807735e04ed0fae9d68','98fc57d52f03e5e5785fed2e694c91ad271c2c29c960a7e6f82734b37c41b034'),
 ('ordinary14-aux-root-bounds-model-draft-independent','173be018cf1a0ae9ebebc14ad297624b9729075b7ffbb87d7cb6e731baab041a','6e250373049d852e0124a6527ce7d1789080b4b35da2077ca1a6faf23eb14db2')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('two_ordinate_impossible X Y eta zeta Delta d hX hY heta hzeta hDelta hmain',
 'lt_of_le_of_ne hkge (Ne.symm hkne)',
 'first_ordinate_large (X*Y*Y) tau (eta+zeta) hm hkgt hfirst'):
 assert f in s,f
n=0
for X in range(1,20):
 for Y in range(1,20):
  c=1+2*Y;aa=X*Y+Y+2;delta=aa*aa-1;N=1+delta*c*c
  assert math.isqrt(N)**2!=N
  m=X*Y*Y
  for k in range(3,40):
   x=1+m*(m+1)*k*k
   if math.isqrt(x)**2==x:assert k>=8*m+4
  n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'fact-level first/main large-k source review; no Lean','finite_parameter_pairs':n,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
