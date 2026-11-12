#!/usr/bin/env python3
"""Independent q=48 p-adic seed and symbolic-interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-x73-q48-toy'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
pin(A/'check.py','b3561e5418acb3df46483f50953efd8de765bd8f100dd43c01be141a57561202')
receipt=pin(A/'result.json','d98fe8d5ff93ca50c9245881264c38c4fdda3b30bae550a79de0e7bc1b832a40')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-direct-x73-q48-toy-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='f4ed74495360dbefd7e6594ce89531c03629d79f3aa5ec9ec048c3507e49b001'
beta,K,MC,MF,J,F,a=47,29,6,7,1,46,1
b=beta*J;q=b+1;C=q-F-a;G=b*(q-F)+a;R=G*(q*q-1)+J*(MC+q*MF);N=(R-1)//2
assert (q,C,G,R,N)==(48,1,95,219127,109563)
assert beta>=46 and beta%2 and 0<MC<beta and 0<MF<2*beta
assert R%4==3 and R+q**3+q+1<=q**4 and pow(2,R,48)==32 and pow(2,R,47)==17
assert (pow(2,R,47)+K-F)%47==0 and (1<<R)>144*N
# Evaluate each coefficient modulo 27 using its 3-adic order and unit,
# rather than constructing the huge exact binomial coefficients.
x=pow(2,R,27);u=1;v=0;total=0
for j in range(N+1):
 total=(total*x+(u*3**v if v<3 else 0))%27
 if j<N:
  aa=2*N-j;bb=j+1
  while aa%3==0:aa//=3;v+=1
  while bb%3==0:bb//=3;v-=1
  assert v>=0
  u=u*(aa%27)*pow(bb,-1,27)%27
assert total==0
# Legendre's formula for the central binomial coefficient; noncentral
# Y terms are multiples of 2^(R-1), so the central valuation is exact.
def v2fact(n):
 result=0
 while n:
  n//=2;result+=n
 return result
central=v2fact(2*N)-2*v2fact(N)-1
assert central==12 and central==N.bit_count()-1 and R-1>central
assert (2**central)*27==q**3

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check.py',receipt)
p=D/'reviews/ordinary14-direct-x73-q5-toy-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'toy p-adic seed and conditional symbolic review; no Lean or full parent exclusion',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'numerator_mod_27':total,'Y_v2':central,'rank':R},sort_keys=True,indent=2))
