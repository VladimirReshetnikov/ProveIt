#!/usr/bin/env python3
"""Source-pinned symbolic comparison of FreeJ and trace74 transport blocks."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
root=Path(__file__).resolve().parents[2]
pins={'Lean/DiophantineConsistency/Compact44/FreeJFirstTransport.lean':'3d806de318b1c798e8b2a31ca14e790a14d09b3996acf9c4c3346d3fc42c2029','Lean/DiophantineConsistency/Compact44/FreeJRootBinding.lean':'7e395c9461414fef818fe1319aad1a31bbd62536ea143c66c8e8134c1ed00b01','research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean':'83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0','research/trace74-carrier-nonnegative-draft/Trace74CarrierNonnegative.lean':'c6ae7bc884d9ab9682d6de7d4214ac1179cfb2bf498b77a2eb589ae5da098b1f'}
def sha(b):return hashlib.sha256(b).hexdigest()
for path,h in pins.items():assert sha((root/path).read_bytes())==h
free=(root/'Lean/DiophantineConsistency/Compact44/FreeJFirstTransport.lean').read_text()
rootbind=(root/'Lean/DiophantineConsistency/Compact44/FreeJRootBinding.lean').read_text()
mask=(root/'research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean').read_text()
carrier=(root/'research/trace74-carrier-nonnegative-draft/Trace74CarrierNonnegative.lean').read_text()
for s in ['let A : V := v 5+(p 1:V)*q','let Bp : V := q*A','let Bn : V := (v 1+v 2)*A+v 1*q','have hBt : Bn<Bp','have hgap : v 1+v 2<q'] :assert s in free
for s in ['let eC : Expr (Fin 12) := .sub (.sub eQ (.var 1)) (.var 2)','let eBt : Expr (Fin 12) := .sub (.mul eC eA) (.mul (.var 1) eQ)']:assert s in rootbind
for s in ['let C : R := v 2','let K0w := K0 + w','let K0wC := K0w * C','let Bt := K0wC - F']:assert s in mask
assert 'theorem graph_B_nonnegative' in carrier and 'theorem graph_F_carrier_bound' in carrier
# Polynomials over Z in ordered variables q,F,C,K0,w; no sampled evaluation.
def add(a,b,sgn=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for x,v in a.items():
  for y,w in b.items():
   m=tuple(i+j for i,j in zip(x,y));c[m]=c.get(m,0)+v*w
 return {m:v for m,v in c.items() if v}
one={(0,0,0,0,0):1}
def var(i):return {tuple(int(j==i) for j in range(5)):1}
q,F,C,K,w=map(var,range(5));alpha=add(add(q,F,-1),C,-1)
A=add(w,mul(K,q));bp=mul(q,A);bn=add(mul(add(F,alpha),A),mul(F,q));freeB=add(bp,bn,-1);freeB_alt=add(mul(C,A),mul(F,q),-1);b74=add(mul(add(K,w),C),F,-1)
assert freeB==freeB_alt
assert add(freeB,b74,-1)==mul(add(q,one,-1),add(mul(K,C),F,-1))
# Independent scalar example: valid positivity, but no root or graph claim.
q0,F0,C0,K0,w0=32,1,32,1,1
assert (K0+w0)*C0-F0==63 and F0+C0>=q0
for path,h in pins.items():assert sha((root/path).read_bytes())==h
print(json.dumps({'status':'PASS','source_pins':pins,'alpha':'q-F-C','freej_B':'C*(w+K0*q)-F*q','trace74_B':'(K0+w)*C-F','difference':'(q-1)*(K0*C-F)','scalar_example':{'q':q0,'F':F0,'C':C0,'K0':K0,'w':w0,'B74':63,'F_plus_C':33},'scope':'External exact polynomial/source comparison; no full graph zero, model-port identification, root-factor transfer or equivalence claim.'},sort_keys=True,indent=2))
