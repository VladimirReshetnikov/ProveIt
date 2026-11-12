#!/usr/bin/env python3
"""Bounded source-token inventory; no Lean, model, or completeness claim."""
import hashlib, json
from pathlib import Path
D = Path(__file__).resolve().parents[2]
files = {
'research/ordinary14-root74-slim-overlay/source/OwnZeroProduct74.lean.src': ('26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db', ['theorem factor_units_of_zero','(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)','v 8*v 8=(m beta v*k v)*(m beta v*k v+k v)+1']),
'research/ordinary14-root74-slim-overlay/source/FactorResidues74.lean.src': ('368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60', ['theorem restricted_residues','theorem aux_shape','theorem strong_shape']),
'research/ordinary14-root74-slim-overlay/source/OwnZeroUnits74.lean.src': ('668fb089dad1ced2867530cb7f95919eb584d49f4aa953903a7e2b6d526de43c', ['theorem unit_iff_one','(pairEval e v).1=(pairEval e v).2+1']),
'research/ordinary14-root74-slim-overlay/source/FirstFactor74.lean.src': ('fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4', ['theorem m_at_least_two','theorem first_eval','theorem first_factor_units']),
'research/ordinary14-root74-slim-overlay/source/Root74PositiveBridge.lean.src': ('f54228acca9fd8db59d25bdd65b3cf4910fb4bd8c7395524c2c4803fdc047e90', ['def expression','theorem positiveBridge : PositiveModelBridge expression']),
'research/ordinary14-root74-slim-overlay/source/CompactPortBoundsSlim.lean.src': ('fb35a320b1521b3005feb597ace302ea9779304839a952b9590f6e0b9a6b4fa4', ['theorem port_bounds','0 < (ports B K L H 0 : V)']),
'research/ordinary14-natural-forced82-ring-bridge-draft/RingNatural82To86.lean': ('08e86ba4044b84a32ad7c2e496c61b454fcd4a5ee963b345d8fe75dc420c120e', ['def down','theorem output_eval','j = 3 ∨ j = 8 ∨ j = 11']),
'research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean': ('e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854', ['def HasThreePredecessors','theorem exists_zero_iff_of_predecessors','(predecessors : ∀ v, InternalZero']),
'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean': ('f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6', ['def positiveShift','def InternalZero','theorem internalZero_positiveShift']),
'Lean/DiophantineConsistency/ModelDifferenceRing.lean': ('5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998', ['theorem internalZero_iff','theorem ι_nonneg','theorem ι_lt_ι','theorem one_le_of_pos']),
'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean': ('3870325628b4148b2825e1af96bbec91ecbb115e2e57a83d580df97ea53f07aa', ['theorem eq_one_or_neg_one_of_mul_eq_one','def Discrete']),
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean': ('d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06', ['def SameNoZero','theorem bridge']),
'Lean/DiophantineConsistency/HAExpressionAssembly.lean': ('15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e', ['def PolynomialBridge','theorem isigma1_equivalence']),
'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean': ('1476d90741c9cae95b164c4de25dcbdf43399347eee97b9031684f9b1a916ce1', ['def PositiveModelBridge','theorem bridge_of_positive']),
'Lean/DiophantineConsistency/IPRAExpressionNative.lean': ('f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8', ['theorem equivalence_of_bridge','nativeTheory ⊢ nativeNoZero e']),
'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean': ('f3755518938e8d3bf4bcb1d33e2dbbfcdc6f2458a414921b1d03ac244503f47c', ['theorem sameNoZero','theorem polynomialBridge','theorem native_equivalence']),
}
for name, (wanted, tokens) in files.items():
    data=(D/name).read_bytes()
    assert hashlib.sha256(data).hexdigest()==wanted, name
    s=data.decode('utf-8')
    for token in tokens: assert token in s, (name,token)
print(json.dumps({'scope':'bounded source and token observations; no Lean elaboration, semantic theorem, or exhaustive absence claim',
                  'pinned_files':len(files), 'tokens_checked':sum(len(t) for _,t in files.values()),
                  'files':{k:v[0] for k,v in sorted(files.items())}},sort_keys=True,indent=2))
