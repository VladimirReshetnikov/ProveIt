#!/usr/bin/env python3
"""Finite controls for the positive-Bt repair argument; no Lean."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def load(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
p=load('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
c=load('research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
assert [row[0] for row in p['source'] if 'r' in row[2:]]==['g31'] and [row[0] for row in c['source'] if 'r' in row[2:]]==['g31']
assert {r[0]:r for r in c['source']}['g31']==['g31','-','g30','r']
controls=0
for m in range(1,35):
 for k in range(3,1500):
  z=1+m*(m+1)*k*k;tau=math.isqrt(z)
  if tau*tau!=z:continue
  kp=(2*m+1)*k-2*tau;tp=(2*m+1)*tau-2*m*(m+1)*k
  assert 2<=kp<k and tp>0 and tp*tp-m*(m+1)*kp*kp==1
  assert k==(2*m+1)*kp+2*tp and k>=8*m+4
  assert 16*z>(4*m*k+k)**2
  controls+=1
assert controls>30
for X in range(1,20):
 for Y in range(1,20):
  a=X*Y+Y;c0=2*Y+1;v=1+((a+2)**2-1)*c0*c0
  assert ((a+2)*c0-1)**2<v<((a+2)*c0)**2
print(json.dumps({'first_pell_descent_controls':controls,'main_k2_controls':19*19,'scope':'conditional signed-candidate positive-Bt repair; no proof Bt>0 or Lean'},sort_keys=True,indent=2))
