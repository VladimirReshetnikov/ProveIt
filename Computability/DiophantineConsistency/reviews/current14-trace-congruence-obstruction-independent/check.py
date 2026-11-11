#!/usr/bin/env python3
import hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-trace-congruence-obstruction'
# Recurrence proof controls without dividing by 3: u_n=2^n psi_(a+2)(n)
# satisfies u_(n+2)=5u_(n+1)-4u_n mod H, so 3u_n=2(4^n−1).
for a in range(0,80):
 H=4*a+3;psi0,psi1=0,1
 for n in range(1,32):
  assert (3*pow(2,n,H)*psi1-2*(pow(4,n,H)-1))%H==0
  psi0,psi1=psi1,2*(a+2)*psi1-psi0
# Exact algebra: 2XP²−2X−2P(X²−1) = −2(X−P)(PX+1).
for X in range(-15,16):
 for P in range(-15,16):assert 2*X*P*P-2*X-2*P*(X*X-1)==-2*(X-P)*(P*X+1)
q,X,Y,R=2,2,16,5;a=Y*(X+1);H=4*a+3;A=a+2;psi0,psi1=0,1
for _ in range(R-1):psi0,psi1=psi1,2*A*psi1-psi0
c=psi1;P=1<<R;num=3*X*c-2*(X*X-1);assert (H,c,num//H)==(195,99970001,3076000) and num%H==0 and X%q==0 and Y%q**3==0 and R+1<X*Y and X!=P and math.gcd(P*X+1,H)==65 and (X-P)*(P*X+1)%H==0
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text())
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'local trace relation does not force X=2^R; q=2 local counterexample, no full zero/current-port/Lean claim'},indent=2))
