#!/usr/bin/env python3
"""Independent source/interface and J=0 signed branch controls, no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-first-norm-J-draft/Residue90FirstNormJ.lean.src','ea7cdcfe04446f9d2fcf50849377e20959fda16df4cadafe7e5b07c1c5c815f6')
pin('research/ordinary13-residue90-first-norm-J-draft/receipt.json','031acc58613a6fd8121710115cba780d59879678449ab6a39d929be9f048aae5')
pin('reviews/ordinary13-residue90-first-norm-gap-independent/result.json','8ae030324aea067d438a05cb7f4f69bad8239797505dd73e15c71b8a5dfb55ef')
n=pin('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src','422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805')
for text in ['theorem J_positive (p : Fin 4 → ℕ)','theorem compact_gamma_of_X (K : ℕ)','(hX : 1≤v 6)','first_ring_norm p v hz','firstRoot p v= -Bt p v','mul_self_eq_zero.mp hsquare','J_positive (ports K) v hz']:
 assert text in s,text
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in n
assert 'ι (v 0*(p 0:V))*(ι (m p v*k v)+ι (k v)+ι (v 8+1)-ι (k v)*Bt p v)-Bt p v' in n
for F in range(1,10):
 for alpha in range(1,10):
  for X in range(10):
   for K in range(10):
    C=1-F-alpha;B=C*(X+K)-F;Z=-B
    assert C<=0 and B<0 and Z>0 and Z*Z>0
print(json.dumps({'scope':'source interface and finite signed J-zero controls; no Lean','J_requires_no_beta_or_X_positivity':True,'compact_gamma_retains_X_positivity':True,'all_ports_represented_natural':True,'physical_kernel_not_bound':True,'lean_elaborated':False},indent=2,sort_keys=True))
