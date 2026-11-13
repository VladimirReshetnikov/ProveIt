#!/usr/bin/env python3
"""Independent exact signed-root source identities; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-root-switch-model-draft/ResidueRootSwitchArithmetic.lean.src','c9adec7548db6d9f1dd2e633e109ccb52b2ccc73490b31bd60bd7d7ae363de13')
pin('research/ordinary13-residue-root-switch-model-draft/receipt.json','46276b017358f08988b62178bc74514b69d3a6bd99ae623985b30158a8ff24b1')
pin('reviews/ordinary13-residue-root-switch-model-independent/result.json','f2c7cd5ccfe670c136b55f07fe557ddcb518539cfabdda599ee4aee97a1a1791')
for x in ['theorem negative_root_at_zero','(hb : 0<b) (hP : 0<P) (hPt : P=b*t) (htau : ell<tau)','linear_combination hs-hz+hpcast','theorem switch_from_zero','⟨2*tau','linear_combination 2*hneg-hz','(hsign : z=ι b*ι tau ∨ z= -(ι b*ι tau))']:
 assert x in s,x
def v(n):return {(n,):1}
def add(a,b,k=1):
 out=a.copy()
 for t,c in b.items():out[t]=out.get(t,0)+k*c
 return {t:c for t,c in out.items() if c}
def mul(a,b):
 out={}
 for x,u in a.items():
  for y,vv in b.items():
   t=tuple(sorted(x+y));out[t]=out.get(t,0)+u*vv
 return {t:c for t,c in out.items() if c}
I={():1};b,P,t,ell,k,tau,z=map(v,['b','P','t','ell','k','tau','z'])
hz=add(add(z,mul(b,add(add(ell,k),mul(k,P),-1)),-1),P)
hs=add(z,mul(b,tau),-1);hp=add(P,mul(b,t),-1);neg=add(z,mul(b,tau))
he=mul(b,add(add(add(ell,mul(k,add(P,I,-1)),-1),t,-1),tau,-1))
assert add(add(hs,hz,-1),hp)==he
flip=add(add(mul(b,add(add(add(ell,k),mul({():2},tau)),mul(k,P),-1)),P,-1),z)
assert add(mul({():2},neg),hz,-1)==flip
for E in range(8):
 for T in range(E+1,E+8):
  for P0 in range(1,8):
   for K in range(6):
    for Q in range(8):assert K*(P0-1)+Q+T>E
print(json.dumps({'scope':'exact signed source proof identities and bounded controls; no Lean','positive_root_excluded_under_explicit_premises':True,'switch_changes_witness':True,'K_bound_not_used_locally':True,'graph_fact_extraction_unproved':True,'lean_elaborated':False},sort_keys=True,indent=2))
