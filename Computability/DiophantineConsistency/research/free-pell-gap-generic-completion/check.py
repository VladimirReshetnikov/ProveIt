#!/usr/bin/env python3
"""Exact small CRT/nonsquare controls for the generic ordinary lemma."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
def unit(A,n):
 d=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+d*y,x+A*y
 return x,y
controls=[]
for A,r,R in ((3,2,5),(4,2,9),(4,3,3)):
 Delta=A*A-1;D0,c=unit(A,r);f,L=1,0
 for _ in range(2*c):f,L=D0*f+Delta*c*L,c*f+D0*L
 assert L%(c*c)==0 and f*f-Delta*L*L==1 and math.gcd(f,A)==1
 S=Delta*L;M=S*S-1;mods=(M,c,f*f);res=(1,(-R)%c,(-c)%(f*f));assert all(math.gcd(mods[i],mods[j])==1 for i in range(3) for j in range(i))
 P=math.prod(mods);V0=sum(a*(P//m)*pow(P//m,-1,m) for a,m in zip(res,mods))%P
 found=None
 for j in range(1,101):
  V=V0+j*P;t=(V*V-1)//M;T=(V+c+f*f*R)//(c*f*f)
  assert V>1 and t>0 and T>0 and (V*V-1)%M==0 and (V+c+f*f*R)%(c*f*f)==0
  if math.isqrt(V*V+t)**2!=V*V+t:found=j;break
 assert found is not None and f*f*(c*T-R)-c==V and V*V-M*t==1
 controls.append({'A':A,'main_index':r,'R':R,'c':c,'first_tested_nonsquare_j':found})
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'controls':controls,'scope':'ordinary generic completion controls, not an actual-port full zero or Lean theorem'},sort_keys=True,indent=2))
