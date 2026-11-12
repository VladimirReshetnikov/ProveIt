#!/usr/bin/env python3
"""Bounded source-interface and arithmetic identity audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
source={
'first':('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5'),
'residues':('Lean/DiophantineConsistency/ArithmeticPellCongruences.lean','75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1'),
'mod':('Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean','b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c'),
'window':('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'),
'mainpell':('Lean/DiophantineConsistency/ArithmeticPellClassification.lean','77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78'),
'power':('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'),
'indices':('Lean/DiophantineConsistency/Compact44/FreeJPellIndices.lean','9e098156d8aff2540e00ee31667954d7288844aad859c9df74f988c7fe0611ac'),
'early':('Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean','ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d'),
'main':('Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean','d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b'),
'direct':('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean','29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd'),
'exact':('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3'),
'graphnorm':('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src','422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805'),
'signed':('research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src','f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a'),
'maingraph':('research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src','8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d'),
'map':('research/ordinary13-residue90-to82-model-draft/Residue90To82Transport.lean.src','bd8ac5e52ff1e82b732b0a0bbeebce88b5d39629a5695aceee5e9a4565436e83'),
'aux':('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean','796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7'),
'auxbounds':('research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean','c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8')}
s={k:pin(*v) for k,v in source.items()}
for k,xs in {'first':['theorem positive_parameter_solution (Q x k : V)','xcoord time (2*(Q-1)+1)=x','2*ycoord time (2*(Q-1)+1)=k'], 'residues':['theorem residue_quotients (time b m : V)','ycoord time b=time+m*s'], 'indices':['magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first'], 'early':['(hi : FreeJIndices p v)','magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first'], 'main':['def FreeJMainCongruence','theorem rank_congruence_from_main','H*(E*q+R+1)+q^5'], 'direct':['theorem direct_main_orientation','U*G+R+1'], 'graphnorm':['theorem first_ring_norm','def firstRoot','theorem rank_representation'], 'signed':['theorem first_natural_norm','theorem main_pair_norm'], 'maingraph':['theorem main_ring_norm','ι (v 6)*ι (Y p v)*ι (q p v)+rankRing'], 'map':['theorem mixed_lower','theorem zero_iff'], 'exact':['theorem indices_ordinary','(hR26 : 26 ≤ R)','theorem exact_ordinary','(hqH : Bez q H 1)'], 'aux':['theorem positive_aux_coordinate_iff','(hQ : 1<Q) (hz : 1<z*z)'], 'auxbounds':['theorem aux_bounds_of_natural_norms'], 'power':['theorem power_bound','theorem projection_quotient']}.items():
 for x in xs:assert x in s[k],(k,x)
# Check q⁴*(2*X*q²*s²)=2*X*(q³*s)², the exact residue divisor.
for q in range(1,10):
 for X in range(1,8):
  for a in range(1,8):assert q**4*(2*X*q*q*a*a)==2*X*(q**3*a)**2
# The early congruence is deliberately weaker than exact 2n=R+1.
q=47;R=4771536;n=(R+1+q**4)//2
assert (2*n)%(q**4)==R+1 and 2*n!=R+1
print(json.dumps({'scope':'pinned source signatures, interfaces and bounded arithmetic controls; no Lean','actual_first_norm_classification_independent_of_core_z':True,'original_FreeJIndices_retains_core_z':True,'q4_early_congruence_not_exact_index':True,'actual_graph_and_port_bindings_remaining':True,'lean_elaborated':False},sort_keys=True,indent=2))
