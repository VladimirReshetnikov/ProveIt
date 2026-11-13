#!/usr/bin/env python3
"""Pin and inspect unelaborated own-zero and conditional-norm source."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 P/'Natural80OwnZeroNorm.lean':'670f8a6e7208afccde1051d72b3154990e1347cbf8d51a3845a89f56f81fcb74',
 D/'research/ordinary14-natural80-jpos-model-draft/Natural80JPos.lean':'6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221',
 D/'research/ordinary14-natural80-partial74-bridge-draft/Natural80Partial74.lean':'942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16',
 D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',
 D/'Lean/DiophantineConsistency/ArithmeticAdaptiveScaledNorms2011.lean':'b3b164e528edf0c2b51eecd994140d30389d80b36ae830dccc286dc0e6bf0863',
 D/'Lean/DiophantineConsistency/ArithmeticAdaptiveTransport2011.lean':'e8b22ad05230a0f0815766adcc989caf66251e9bad34eb524da83f9155b5ee24',
}
sources={}
for p,h in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);sources[p.name]=b.decode()
s=sources['Natural80OwnZeroNorm.lean']
for x in ('theorem units_of_80_zero','(hbeta : (p 0 : DiffRing V)=ι beta)',
          '(hK : (p 1 : DiffRing V)=ι K)','(hb : 0<beta) (hKpos : 0<K)',
          'Natural80JPosDraft.J_pos_of_zero','internalZero_iff_partial p v',
          'restricted_residues p u','factor_units_of_zero p beta u',
          'theorem main_norm_of_unit','(hroot : Equivalent',
          '(hrhs : pairEval (mainRhs p) u=(rhs,0))',
          'unit_square_norm','magnitude_equivalent',
          '#print axioms DiophantineConsistency.Natural80OwnZeroNormDraft.units_of_80_zero',
          '#print axioms DiophantineConsistency.Natural80OwnZeroNormDraft.main_norm_of_unit'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
assert 'theorem unit_square_norm' in sources['ArithmeticAdaptiveScaledNorms2011.lean']
assert 'theorem magnitude_equivalent' in sources['ArithmeticAdaptiveTransport2011.lean']
print(json.dumps({'scope':'pinned source interfaces only; no Lean or model theorem',
                  'represented_beta_and_positive_k0_explicit':True,
                  'main_root_and_rhs_bindings_explicit_assumptions':True,
                  'axiom_print_commands_not_executed':2},sort_keys=True,indent=2))
