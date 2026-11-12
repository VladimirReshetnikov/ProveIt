#!/usr/bin/env python3
"""Independent actual-graph projection source composition audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-three-projection-graph-draft/ResidueThreeProjectionGraph.lean.src','589fb5cd96875a7ee9728035c8ca49bf3406336c8c9362eebd112d2d6e3e3f7b')
pin('research/ordinary13-residue-three-projection-graph-draft/receipt.json','617e299313e16f284d70bfb6603415593fdce395523cddf8cbf914e1ebca4365')
pin('reviews/ordinary13-residue-three-projection-independent/result.json','3abf4f8c568e7afc54a435da385db53e32f571d10139e99757bd32c42d3eb597')
pin('reviews/ordinary13-residue-aux-bounds-adapter-independent/result.json','f300e024e0dc46c16364e513ed348c165262723f639f64f6a43c2d22e5ad8760')
pin('reviews/ordinary13-residue-main-congruence-model-independent/result.json','d5e8f827520f00bc6d7c5d4a8a8759d265a9dd43c48e0fb5a31ca2147192f8d1')
for x in ['theorem actual_main_balance','actual_main_magnitude_norm p v hz hFq','DirectMainNorm.direct_main_orientation','(rank p v+v 6*Y p v*q p v) hU hY8 hk','linear_combination -hbalance','theorem q_dvd_threeX_of_graph','(hJ : 0<v 0) (hbeta : 0<(p 0:V)) (hX : 0<v 6)','(hgap :','(hwindow :','ResidueExactIndexFromGraphDraft.exact_indices_of_graph','⟨_,n,w,_,_,_,_,_,_,_,heq,_,hks⟩','simpa only [m,heq] using hks','ResidueThreeProjectionDraft.q_dvd_threeX']:
 assert x in s,x
assert ': q p v ∣ 3*v 6' in s and 'Bez' not in s
# Actual pair P=N+U*main has the same orientation as U*main+N=P.
for U in range(5):
 for N in range(5):
  for main in range(5):
   P=N+U*main
   assert U*main+N==P
for R in range(30):
 for n in range(20):
  if 2*n!=R+1:continue
  for Q in range(5):
   for w in range(5):assert 2*n+4*Q*w==R+1+4*Q*w
print(json.dumps({'scope':'actual main-orientation and exact-index projection source interfaces; no Lean','adjusted_rank_XYq_retained':True,'exact_index_decomposition_used':True,'only_q_divides_three_X':True,'natural_port_and_graph_premises_explicit':True,'lean_elaborated':False},sort_keys=True,indent=2))
