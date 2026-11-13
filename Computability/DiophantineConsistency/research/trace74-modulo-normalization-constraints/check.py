#!/usr/bin/env python3
"""Exact free-ring checks for a proposed same-q, same-k chart normalization."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
root=Path(__file__).resolve().parents[2]
pins={'research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean':'83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0','research/trace74-guardfree-adjacent-draft/Trace74OffsetDiv.lean':'db50f4b5c7c4c9e0bef199a0bbe3681d6996d58162dcb6c5bdbeaa64133f1092'}
def sha(b):return hashlib.sha256(b).hexdigest()
for p,h in pins.items():assert sha((root/p).read_bytes())==h,(p,sha((root/p).read_bytes()))
# Free commutative polynomial ring over Z; q,F,C,a,b,K,w,MC,MF,J,c,f,T,h,D,H,L,N,Z0.
names=['q','F','C','a','b','K','w','MC','MF','J','c','f','T','h','D','H','L','N','Z0'];size=len(names);zero=(0,)*size
one={zero:1}
def var(i):return {tuple(int(j==i) for j in range(size)):1}
def add(x,y,sgn=1):
 out=dict(x)
 for m,v in y.items():out[m]=out.get(m,0)+sgn*v
 return {m:v for m,v in out.items() if v}
def sub(x,y):return add(x,y,-1)
def mul(x,y):
 out={}
 for m,a0 in x.items():
  for n,b0 in y.items():
   key=tuple(i+j for i,j in zip(m,n));out[key]=out.get(key,0)+a0*b0
 return {m:v for m,v in out.items() if v}
def plus(*xs):
 z={}
 for x in xs:z=add(z,x)
 return z
q,F,C,a,b,K,w,MC,MF,J,c,f,T,h,D,H,L,N,Z0=map(var,range(size))
Fp=sub(F,mul(q,a));Cp=sub(C,mul(q,b));q2=mul(q,q)
def rank(F0,C0):return plus(mul(sub(mul(q,sub(q,F0)),C0),sub(q2,one)),mul(plus(MC,mul(q,MF)),J))
R=rank(F,C);Rp=rank(Fp,Cp);dR=sub(Rp,R)
assert dR==mul(mul(q,sub(q2,one)),plus(mul(q,a),b))
def B(F0,C0):return sub(mul(plus(K,w),C0),F0)
B0=B(F,C);Bp=B(Fp,Cp);dB=sub(Bp,B0)
assert dB==mul(q,sub(a,mul(plus(K,w),b)))
# Generic same-c/f change, independent fresh dT/dN/dR/dB symbols encoded by T,N,Rp,Bp.
dT=Z0; dN=N
Vold=sub(mul(f,sub(mul(c,T),R)),c);Vnew=sub(mul(f,sub(mul(c,plus(T,dT)),Rp)),c)
assert sub(Vnew,Vold)==mul(f,sub(mul(c,dT),dR))
# Direct Z difference by expanding a generic baseline Z; e'−e=−dR, L is unchanged.
e=MC; n0=MF; k0=J
Z=lambda n,B0,e0:sub(mul(mul(h,D),plus(mul(H,sub(n,mul(L,B0))),k0)),mul(H,plus(mul(D,B0),mul(h,e0))))
Zold=Z(n0,B0,e);Znew=Z(plus(n0,dN),Bp,sub(e,dR));dZ=sub(Znew,Zold)
assert dZ==mul(H,plus(mul(mul(h,D),dN),sub(mul(h,dR),mul(plus(mul(mul(h,D),L),D),dB))))
# q=2 and a=1,b=0 show the q^4 condition can fail; not a graph-zero example.
q0=2;dR0=q0**2*(q0**2-1)
assert dR0==12 and dR0%(q0**4)!=0
for p,x in pins.items():assert sha((root/p).read_bytes())==x
print(json.dumps({'status':'PASS','pins':pins,'rank_change':'q(q²−1)(aq+b)','B_change':'q(a−(K+w)b)','V_change':'f(c*dT−dR)','Z_change':'H[hD*dN−(hDL+D)*dB+h*dR]','sample_q2_rank_change':12,'sample_q2_q4':16,'scope':'External free-ring identities and a scalar nondivisibility sample; graph-zero necessity uses separately checked offset theorem, no witness transformation or global impossibility.'},indent=2,sort_keys=True))
