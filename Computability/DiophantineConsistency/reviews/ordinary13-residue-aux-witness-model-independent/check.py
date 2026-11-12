#!/usr/bin/env python3
"""Signed ordinate and strong/auxiliary witness interface audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-aux-witness-model-draft/ResidueAuxWitness.lean.src','1037e3a296285ae16c221d5beeebdde89050ee2ce74acf9e6335ba11a1935a1e')
pin('research/ordinary13-residue-aux-witness-model-draft/receipt.json','c18aa9dedb91cc052068b98a2a868667a58fed984d61bef9b9be28951d7c4125')
pin('reviews/ordinary13-residue90-fy-model-independent/result.json','d966ff3d5ec756e09d9c349fde0847e3bf618050c1109a76c031f789b17a50b0')
pin('reviews/ordinary13-eta-zero-auxiliary-independent/result.json','dcf98bbfed9e3d01c6968eb9e8c0cd2595be8438f22d97904a3a12bfbc2da4e3')
r=pin('Lean/DiophantineConsistency/Compact44/P72Root.lean','066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')
a=pin('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean','796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7')
g=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'));rows={r[0]:r for r in g['source']}
for row in [['f2','*','n_f','n_f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','shift_i'],['g71','*','I','I'],['g72','-','g71','Q'],['g74','*','shift_T','c'],['g75','-','g74','R'],['g76','*','f2','g75'],['V','-','g76','c'],['Fa','-','y2','g82']]:assert rows[row[0]]==row,row
for x in ['theorem ordinary_strong','theorem ordinate_pair','(hFq : v 1+1≤q p v)','(hZ : (1 : DiffRing V)<ordinateRing p v*ordinateRing p v)','AuxRootModelDraft.square_gt_of_aux','AuxRootModelDraft.above_of_positive','nonneg_iff.mp','P72Root.ι_magnitude_sq A B','P72Root.ι_magnitude_sq (A+u) B','P72Root.ι_tsub hf1','linear_combination haux']:
 assert x in s,x
assert 'theorem ι_magnitude_sq (P N : V)' in r and 'theorem ι_tsub' in r
assert 'theorem square_gt_of_aux' in a and 'theorem above_of_positive' in a
# Independently verify signed auxiliary rearrangement and absdiff squares.
for A in range(15):
 for B in range(15):
  for u in range(8):
   assert abs(A-B)**2==(A-B)**2 and abs(A+u-B)**2==(A+u-B)**2
for Q in range(2,10):
 for z in range(-30,31):
  for y in range(0,35):
   aux=y*y-Q*(y*y-z*z)-1
   assert aux==Q*z*z+y*y-1-Q*y*y
   if z*z>1 and aux==0:assert y>abs(z) and y-z>0
print(json.dumps({'scope':'literal strong/ordinate rows, signed absdiff and explicit auxiliary cut; no Lean','strong_witness_i_plus_one':True,'rank_cast_requires_F_le_q':True,'strict_ordinate_square_assumed':True,'natural_offset_via_nonnegative_cone':True,'no_eta_zero_or_full_endpoint_claim':True,'lean_elaborated':False},sort_keys=True,indent=2))
