#!/usr/bin/env python3
"""Independent q=10 toy seed and symbolic-interface review; no Lean."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-x73-q10-toy'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
pin(A/'check.py','13a7aa83700c54db19d319a5faf1310b83703d2c5d8dbc9bd6d81fa911ac5b8b')
receipt=pin(A/'result.json','a115675d797e655684a0a83cfbf7046bb8b90084a6d98cfeedf6489a15d70e06')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-direct-x73-q10-toy-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='95516b5a7f42eeb4599c46af34f01c2e1dd59aaf36e2a55d330c0d069dc02abb'
beta,K,MC,MF,J,F,a=3,5,2,2,3,1,2
b=beta*J;q=b+1;C=q-F-a;G=b*(q-F)+a;R=G*(q*q-1)+J*(MC+q*MF);N=(R-1)//2
assert (q,C,G,R,N)==(10,7,83,8283,4141)
assert 0<MC<beta and 0<MF<2*beta and R%4==3 and R+q**3+q+1<=q**4
X=1<<R;assert X>144*N and X%10==8 and X%9==8
B=C*(X+K)-F;assert B%9==0
h=1+B//9;assert h>0 and C*(X+K)+q-F-b*h==1
# Sum from the central binomial coefficient toward the leading term,
# using exact integer coefficient recurrences and modular powers.
coefficient=math.comb(2*N,N); power=1; total=0
for j in range(N+1):
 total=(total+coefficient*power)%2000
 if j<N:
  coefficient=coefficient*(N-j)//(N+j+1)
  power=power*(X%2000)%2000
assert total==0
# Since 100|Y, U=100Y divides X*Y², independent of q|X.
for y in (100,1000,2100):assert (X*y*y)%(100*y)==0

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check.py',receipt)
p=D/'reviews/ordinary14-direct-x73-q5-toy-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'toy modular seed and conditional symbolic review; no Lean or full parent exclusion',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'numerator_mod_2000':total,'rank':R},sort_keys=True,indent=2))
