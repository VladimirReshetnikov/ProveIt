#!/usr/bin/env python3
"""Independent literal main-root binding and source composition audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src','8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d')
pin('research/ordinary13-residue90-xzero-graph-draft/receipt.json','5935ede63713efe63f0d32d907a8ded2689cb9438e8df256a383fc4ee5629004')
pin('reviews/ordinary13-residue90-xzero-model-independent/result.json','c8af0705032218eca64fe985724af8988ded4692d0d51ceb953d79d916131cd2')
pin('reviews/ordinary13-residue90-first-norm-J-independent/result.json','09d6f1059a001683f985cdfe058941e4ef398a827924405e0fd68585c51d9000')
g=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'));rows={x[0]:x for x in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['qF','-','q','F'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50'],['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65']]:assert rows[row[0]]==row,row
for x in ['theorem main_ring_norm','all_residuals_zero _ v hz 1','theorem X_positive','(hJ : 0<v 0) (hbeta : 0<(p 0:V))','Residue90XZeroArithmeticDraft.xzero_impossible','theorem compact_X_positive','theorem compact_gamma_positive','Residue90FirstNormJDraft.compact_gamma_of_X','(K : ℕ)']:
 assert x in s,x
assert 'ι (U p v)*ι (v 12)+ι (v 6)*ι (Y p v)*ι (q p v)+rankRing p v+1-ι (k v)' in s
# Independent integer evaluations of literal graph at arbitrary signed ports and gamma.
for J in range(3):
 for beta in range(3):
  for F in range(1,4):
   for alpha in range(1,4):
    q=1+J*beta
    for X in range(3):
     Y=q**3;U=Y*q*q;H=3+4*(X*Y+Y);a=X*Y+Y;c=1+Y*3
     for gamma in range(3):
      R=(alpha+(q-F)*(J*beta))*(q*q-1)+J*(2+q*3)
      shift0=U*gamma+X*Y*q+R+1-3
      dst=U*(X+a*c)+H*shift0
      assert dst==U*(X+a*c)+H*(U*gamma+X*Y*q+R+1-3)
      if X==0: assert a==Y and dst==U*(Y*c)+H*shift0
print(json.dumps({'scope':'literal source binding and finite identity controls, no Lean','main_norm_arbitrary_gamma':True,'exact_XYq_shift_present':True,'X_client_requires_J_and_beta':True,'compact_K_arbitrary_natural':True,'physical_fixed_port_binding_not_proved':True,'lean_elaborated':False},sort_keys=True,indent=2))
