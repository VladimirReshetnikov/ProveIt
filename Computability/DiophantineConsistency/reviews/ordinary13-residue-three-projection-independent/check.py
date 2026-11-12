#!/usr/bin/env python3
"""Independent exact signed divisibility certificates and source premises; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src','d4c30dc20ef93cbcad180d4ba350d77d0c0534e8ef485254509a9c1604026cf2')
pin('research/ordinary13-residue-three-projection-model-draft/receipt.json','394e0861f7d66cc45269b4a0ed0aa350c2658abe9084871fd20db4dd9adcff8f')
r=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885')
for x in ['theorem q_dvd_threeX','(hq : 0<q) (hs : 0<s) (hY : Y=q*(q*q)*s)','(hindex : k=R+1+4*(X*Y*Y)*w)','linear_combination -hBalR+ι H*hIdxR+4*ι H*ι X*ι w*hYsq','mul_left_cancel₀ (ne_of_gt hSRpos)','z-4*(ι q*ι q*ι s)*(ι X+1)*ι X','Trace75IntegralTransport.natural_dvd_of_signed q (3*X)']:
 assert x in s,x
assert 'theorem natural_dvd_of_signed (a b : V)' in r and 'Bez' not in s
# Free polynomial ring verifies certificates with signed witnesses.
def v(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for t,c in b.items():d[t]=d.get(t,0)+k*c
 return {t:c for t,c in d.items() if c}
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,vv in b.items():
   t=tuple(sorted(x+y));d[t]=d.get(t,0)+u*vv
 return {t:c for t,c in d.items() if c}
def product(*terms):
 out={():1}
 for x in terms:out=mul(out,x)
 return out
one={():1};four={():4};three={():3};U,H,X,Y,q,S,c,a,gamma,main,ss,w,k,R,z=map(v,['U','H','X','Y','q','S','c','a','gamma','main','s','w','k','R','z'])
hBal=add(add(product(U,main),product(H,k)),add(product(U,add(X,product(a,c))),product(H,add(add(product(U,gamma),product(X,Y,q)),add(R,one)))),-1)
hIdx=add(k,add(add(R,one),product(four,X,Y,Y,w)),-1)
hYsq=add(product(Y,Y),product(U,q,ss),-1)
witness=add(add(add(add(main,product(four,H,X,q,ss,w)),X,-1),product(a,c),-1),product(H,gamma),-1)
target=add(product(H,X,Y,q),product(U,witness),-1)
certificate=add(add({t:-c0 for t,c0 in hBal.items()},product(H,hIdx)),product(four,H,X,w,hYsq))
assert target==certificate
# H=3+4*q³*s*(X+1): signed q-divisibility witness for 3X.
H0=add(three,product(four,q,q,q,ss,add(X,one)));hHX=add(product(H0,X),product(q,z),-1)
hthree=add(product(three,X),product(q,add(z,product(four,q,q,ss,add(X,one),X),-1)),-1)
assert hHX==hthree
for q0 in range(1,8):
 for s0 in range(1,8):
  Y0=q0**3*s0;assert Y0>0 and Y0*q0>0
print(json.dumps({'scope':'exact free-ring signed witness certificates and source premises; no Lean','signed_balance_certificate_correct':True,'positive_Yq_cancellation_explicit':True,'q_divides_3X_only':True,'no_bezout_or_q_divides_X_assumed':True,'lean_elaborated':False},sort_keys=True,indent=2))
