#!/usr/bin/env python3
"""Independent natural-rank lower-bound interface and finite controls; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-rank-lower-model-draft/ResidueRankLower.lean.src','86fd995a873fedeeeaa79a2a476276870a4a1be26bfc0a273ce052600e941b2f')
pin('research/ordinary13-residue-rank-lower-model-draft/receipt.json','a92c2cd45412312d719338aaa64b0f14eaeeaed6e2da3ae6dc802ad97dc30209')
g=pin('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src','422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805')
for x in ['theorem scalar_rank_at_least_40','(hF : 0<F) (ha : 0<alpha) (hgap : F+alpha<q)','tsub_add_cancel_of_le hq1','tsub_add_cancel_of_le hFq','tsub_add_cancel_of_le hq2one','mul_le_mul hqm2 hqF2','mul_le_mul h5 h8','theorem graph_rank_at_least_40','theorem graph_rank_at_least_26']:
 assert x in s,x
assert '((q p v-1)*(q p v-(v 1+1))+(v 2+1))*(q p v*q p v-1)+' in g
checks=0;minimum=None
for q in range(3,22):
 for F in range(1,q):
  for alpha in range(1,q-F):
   assert 1<=q and F<=q and 1<=q*q
   qm=q-1;qf=q-F;z=q*q-1
   assert qm+1==q and qf+F==q and z+1==q*q
   assert 2<=qm and 2<=qf and 5<=qm*qf+alpha and 8<=z
   for MC in range(3):
    for MF in range(3):
     for J in range(3):
      rank=(qm*qf+alpha)*z+(MC+q*MF)*J
      assert rank>=40
      minimum=rank if minimum is None else min(minimum,rank);checks+=1
assert minimum==40
print(json.dumps({'scope':'exact source cut and finite lower-bound controls; no Lean','rank_at_least_40_under_positive_F_alpha_and_gap':True,'minimum_40_in_finite_box':True,'truncated_subtraction_bounds_explicit':True,'graph_gap_not_proved':True,'finite_controls':checks,'lean_elaborated':False},sort_keys=True,indent=2))
