#!/usr/bin/env python3
"""Independent extraction signs, source interfaces, bounded controls; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src','01d086c7d25b266f2385d9084f24ee8b9fc15e605eee97503a9b7329396e78f3')
pin('research/ordinary13-residue-root-switch-extraction-draft/receipt.json','def4c853fc953a9ac1da10f85532821bcc1dd3c5d4990ef0f8872ad3e8f1eb73')
pin('reviews/ordinary13-residue-root-switch-model-draft-independent/result.json','ee962267652ae67f6cb059b1cd4820fb59a573b10fdd4a8eb794df71e19c8d01')
mag=pin('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c')
quo=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885')
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in mag
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m)' in quo
assert 'theorem natural_dvd_of_signed (a b : V)' in ref
for x in ['theorem P_positive','(hb : 0<b) (hk : 2≤k)','theorem root_data','nonneg_iff.mp (le_of_lt hPpos)','ReducedNormSigned.natural_magnitude_square','ArithmeticAdaptiveQuotients2011.scaled_quotient','linear_combination hz-hw','Trace75IntegralTransport.natural_dvd_of_signed','theorem positive_replacement']:
 assert x in s,x
# Exact divisor certificate: hz=z-b*A+P and hw=z-b*w.
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(sorted(x+y));d[m]=d.get(m,0)+u*v
 return {m:v for m,v in d.items() if v}
b,P,A,z,w=map(atom,['b','P','A','z','w'])
hz=add(add(z,mul(b,A),-1),P);hw=add(z,mul(b,w),-1)
assert add(hz,hw,-1)==add(P,mul(b,add(A,w,-1)),-1)
for bb in range(1,8):
 for E in range(10):
  for k in range(2,10):
   assert (E+k)**2>1+E*(E+k)
   for P0 in range(-5,1):
    Z=bb*(E+k-k*P0)-P0
    assert Z>=bb*(E+k)>0 and Z*Z>bb*bb*(1+E*(E+k))
print(json.dumps({'scope':'source interfaces, exact signed-divisor certificate and finite norm controls; no Lean','positive_P_before_natural_representation':True,'signed_divisibility_reflected_to_naturals':True,'positive_replacement_not_original_r':True,'no_K0_bound_locally':True,'graph_binding_unproved':True,'lean_elaborated':False},sort_keys=True,indent=2))
