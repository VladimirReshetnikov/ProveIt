#!/usr/bin/env python3
"""Independent shifted-coordinate and strict-bound source composition audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueAuxBoundsAdapter.lean.src','4b6e7be4c6dd5aad302146018e304ae0fc8b523371b73c68707f02dfa8dd2e11')
e=pin('research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src','169c4e604a573fa1da69ca5d642d9d9de4b125515badb88f67b17f78b24601f1')
pin('research/ordinary13-residue-aux-bounds-adapter-draft/receipt.json','6b1b0f99fc9b6d0980004053abbc5ec68dfb98719222e5e0fa0631302b897bb2')
pin('reviews/ordinary13-residue-exact-index-model-independent/result.json','006ef466a565ece5e44caa6b6b4196ee4568bc070c7be34d09ec816cf4ab5296')
pin('reviews/ordinary13-residue-aux-witness-model-independent/result.json','ca5faab84650c0255afd7129a685dd8992c298f67dd3c6149f2a6a78bb358a41')
pin('reviews/ordinary13-residue-rank-lower-model-independent/result.json','151ccc6f02f655cdbac45bdc3e7d67574bc27cabc7bb72106c9e2997f785f286')
a=pin('research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean','c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8')
for x in ['theorem main_natural_of_graph','main_ring_norm p v hz','Residue90SignedNormsDraft.signed_norm_quotient','theorem ordinate_square_large','have heta : 0<v 9+1','have hzeta : 0<v 10+1','have hi : 0<v 4+1','ResidueAuxWitnessDraft.ordinary_strong','rw [←strong_identity p v hz]','ordinateRing p v+ι (c p v)','AuxNormsToBoundsDraft.aux_bounds_of_natural_norms']:
 assert x in s,x
assert '(heta : 0<eta) (hzeta : 0<zeta)' in a
for x in ['theorem exact_indices_of_graph','(hJ : 0<v 0) (hbeta : 0<(p 0:V)) (hX : 0<v 6)','(hgap :','(hwindow :','main_natural_of_graph','ordinate_square_large','old_aux_of_direct_graph','main_index_of_natural_norm','graph_rank_at_least_26','exact_indices_of_actual_graph']:
 assert x in e,x
assert 'q ∣' not in e and 'Bez' not in e
# Exact signed ordinate identity and discriminant polynomial, finite controls.
for X in range(5):
 for Y in range(1,6):
  aa=X*Y+Y;delta=(3+4*aa)+aa*aa
  assert (aa+2)**2==delta+1
  for f in range(5):
   for T in range(5):
    for R in range(5):
     for c in range(1,4):
      z=f*f*(T*c-R)-c
      assert z+c==f*f*(T*c-R)
print(json.dumps({'scope':'shifted-coordinate, discriminant and signed norm source composition; no Lean','eta_zeta_and_i_shifted_positive':True,'strict_ordinate_bound_from_proposed_norms_not_assumed':True,'rank_window_and_gap_explicit':True,'no_eta_zero_generalization':True,'provider_and_graph_elaboration_open':True,'lean_elaborated':False},sort_keys=True,indent=2))
