#!/usr/bin/env python3
"""Independent signed divisibility certificate review; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src','144b5447d8fde7f6384e3fb5ae8311bc051bf563190d204db3dad4810df5914b')
pin('research/ordinary13-residue90-xzero-model-draft/receipt.json','e77b05aced2e3f36b8e76aaa1b446f2a7bc92f4bd8aedfbb0239d9b0c3cd454a')
sq=pin('Lean/DiophantineConsistency/ModelRelationCombining.lean','559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6')
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885')
assert 'theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0) (h : m ^ 2 ∣ s ^ 2) : m ∣ s' in sq
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in ref
for x in ['theorem cancel_modulus','linear_combination -U*hnorm+(d+a*c)*hw','theorem modulus_dvd_scale','linear_combination hshape-hd','mul_left_cancel₀ (mul_ne_zero hU hU) hfactorScaled','theorem xzero_impossible','(hq : 2≤q) (hY : q^3≤Y)','linear_combination -4*hw','Trace75IntegralTransport.natural_dvd_of_signed']:
 assert x in s,x
# Check each certificate in the free integer polynomial ring.
def v(n):return {(n,):1}
def plus(a,b,k=1):
 out=a.copy()
 for t,c in b.items():out[t]=out.get(t,0)+k*c
 return {t:c for t,c in out.items() if c}
def mul(a,b):
 z={}
 for x,u in a.items():
  for y,vv in b.items():
   t=tuple(sorted(x+y));z[t]=z.get(t,0)+u*vv
 return {t:c for t,c in z.items() if c}
one={():1};U,H,d,a,c,w,q,Y,z,t=map(v,['U','H','d','a','c','w','q','Y','z','t']);ac=mul(a,c);dm=plus(d,ac,-1);dp=plus(d,ac);cc=mul(c,c)
hnorm=plus(mul(dm,dp),plus(one,mul(H,cc)),-1);hw=plus(mul(U,dm),mul(H,w),-1)
expected=plus(U,mul(H,plus(mul(w,dp),mul(U,cc),-1)),-1)
assert plus(mul(U,hnorm),mul(dp,hw),-1)=={t:-v for t,v in expected.items()}
hshape=plus(plus(z,mul(U,ac),-1),mul(H,t),-1);hd=plus(z,mul(U,d),-1)
assert plus(hshape,hd,-1)==plus(mul(U,dm),mul(H,t),-1)
# Scale identity after substituting U=Y*q², H=3+4Y, U=H*w.
qq=mul(q,q);three={():3};four={():4};HH=plus(three,mul(four,Y));UU=mul(Y,qq);hw0=plus(UU,mul(HH,w),-1)
lhs=plus(mul(three,qq),mul(HH,plus(qq,mul(four,w),-1)),-1)
assert lhs=={term:-4*coef for term,coef in hw0.items()}
for Q in range(2,30):
 for YY in range(Q**3,Q**3+10):
  assert 0<3*Q*Q<3+4*YY
print(json.dumps({'scope':'free-ring certificate identities, signed reflection interface and finite size controls; no Lean','signed_quotient_either_sign':True,'U_nonzero_required':True,'main_norm_and_scale_hypotheses_explicit':True,'graph_extraction_not_proved':True,'lean_elaborated':False},sort_keys=True,indent=2))
