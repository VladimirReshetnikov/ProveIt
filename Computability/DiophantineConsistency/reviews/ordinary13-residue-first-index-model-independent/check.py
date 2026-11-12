#!/usr/bin/env python3
"""Independent early-index signature, quotient and congruence audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src','0b69fb042a913232ef9f4a92757107f60d8a590f855176134587939012b1b93b')
pin('research/ordinary13-residue-first-index-model-draft/receipt.json','0a6fa5d8a83af0132714f600742bccc91c78f9a3e65fe96b0aef3cae0ea9ef1b')
pin('reviews/ordinary13-residue82-first-index-interface-audit/result.json','eb01dc5f085d6d8519cbd9af512d4a87bc927b7b5d738f009e36ebb98b10bcec')
pin('reviews/ordinary13-residue82-firstindex-companion-obstruction-independent/result.json','941b867d22f3085e8e7ab65ee872acc8e185aab7c02f054cc2be05b65738846a')
f=pin('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
r=pin('Lean/DiophantineConsistency/ArithmeticPellCongruences.lean','75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1')
mm=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean','b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c')
assert 'theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)' in f
assert 'theorem residue_quotients (time b m : V) (hm : m∣b+1)' in r
assert 'theorem magnitude_mod (p : Pair V) (m : V) (hm : 0<m)' in mm
for x in ['(hq : 0<q) (hX : 0<X) (hYpos : 0<Y) (hY : Y=q^3*s)','(hR24 : 24≤R) (hwindow : R+q^3+q+1≤q^4)','(hcong : q^4 ∣ magnitude (R+1,k))','positive_parameter_solution Q tau k','residue_quotients n B (q^4)','residue_quotients n B (2*Q)','(2*n)%(q^4)=R+1','k=2*n+4*Q*w']:
 assert x in s,x
assert 'core.z' not in s.split('theorem early_index_of_natural_norm',1)[1]
# All stated q^4 and 2Q quotient formulas, and modular orientation, in
# finite controls; general reasoning is recorded in the README.
for q in range(2,10):
 for X in range(1,5):
  for a in range(1,5):
   Y=q**3*a;Q=X*Y*Y;B=2*(Q-1)+1
   assert B+1==2*Q==q**4*(2*X*q*q*a*a)
   for n in range(1,20):
    for t in range(4):
     k=2*n+q**4*(2*t)
     R=(2*n)%(q**4)-1
     if R>=0:assert (R+1)%(q**4)==k%(q**4)
q=47;R=4771536;n=4825609
assert (2*n)%(q**4)==R+1 and 2*n!=R+1
print(json.dumps({'scope':'source signatures and finite arithmetic controls; no Lean','actual_natural_norm_not_core_z':True,'q4_and_twoQ_recurrence_divisors_correct':True,'rank_congruence_orientation_correct':True,'does_not_claim_exact_index':True,'graph_norm_rank_port_cuts_remain_premises':True,'lean_elaborated':False},sort_keys=True,indent=2))
