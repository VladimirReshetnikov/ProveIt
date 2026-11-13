#!/usr/bin/env python3
"""Independent 87 own-zero q divides 3X source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-divides-3x-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','fff9bc8b44b63992d0b5d6985533f6af5f146dff550ac7031ca2654f8e5bea03')
s=pin(A/'Divides3X87.lean','cf1ea4c6174d70fe784071b51139967482fcb412ee8e2844a52589affb011b01').decode()
pin(A/'check_source.py','bd72a2174d026c0decd6664821fc3cca9828235e8e1f114247a62292d4654887')
receipt=pin(A/'observation.json','8557a97e5374c63335f10b254cc24e784e328daff36647caabffa5ca30a9f118')
for f in ('P72ExactIndices87Draft.exact_indices p beta K MC MF v',
 'FirstQuotient87Draft.quotient_and_root','let W : V := 4*xx*qq*s0*s',
 'have hk : kk=R+1+uu*W','have hqY : 0<qq*yy',
 'apply mul_left_cancel₀ (ne_of_gt hqY)','let D : V := 4*(qq*qq)*s0*(xx+1)',
 'have hH : H=3+qq*D','q beta v∣3*X v'):
 assert f in s,f
n=0
for q in range(2,14):
 for s0 in range(1,5):
  Y=q**3*s0;U=Y*q*q
  for X in range(1,8):
   H=3+4*Y*(X+1);factor=4*q*q*s0*(X+1)
   assert H==3+q*factor
   for w in range(5):
    W=4*X*q*s0*w
    assert 4*X*Y*Y*w==U*W
    assert (H*X-3*X)%q==0;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-87-p72-exact-indices-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero q divides 3X source projection review; no Lean','finite_factorization_cases':n},sort_keys=True,indent=2))
