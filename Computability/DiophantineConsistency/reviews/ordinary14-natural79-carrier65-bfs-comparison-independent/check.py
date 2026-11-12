#!/usr/bin/env python3
"""Pinned independent target, composition direction, and namespace review; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/Natural79Carrier65BFSComparison.lean':'48d46d534b6d0834546e5e169af515d942ad1e43fbff2f6db40ab29b2a16c5e8',
'research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/check_source.py':'b1d158b7f1722b6f3c71f004909735bc81a65b8822f7341de9bf8012c25440f8',
'research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/receipt.json':'f15ea245e0cf6711fcbad559da2ea04dd623bb4ab1b017ea73e0b09c0203ea32',
'research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean':'9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6',
'Lean/DiophantineConsistency/BFS943/IPRACarrier65BFS943.lean':'6ef47f75856066859044f38a91ad066e294a1679fcdd342fa35eb66f2c50eae9',
'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean':'11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c',
'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean':'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'Lean/DiophantineConsistency/IPRAStandardTheory.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean':'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9',
'Lean/DiophantineConsistency/IPRAOrderErasure.lean':'d14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6'}
s={}
for p,h in pins.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[Path(p).name]=b.decode()
def has(n,*xs):
 for x in xs:assert x in s[n],(n,x)
draft=s['Natural79Carrier65BFSComparison.lean']
assert re.search(r'^open AdaptiveEquationSyntax2011\b',draft,re.M)
has('AdaptiveEquationSyntax2011.lean','namespace DiophantineConsistency.AdaptiveEquationSyntax2011',
 'def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=\n  e.subst (fun i => Expr.var i + Expr.constant 1)')
has('IPRAExpressionNative.lean','def nativeNoZero {n : ℕ} (e : Expr (Fin n)) : Sentenceᵢ language')
has('Natural79Endpoint.lean','def expression : Expr (Fin 14) := (P79NaturalForcedW.graph CompactSymbolicModelIff.p).output',
 'theorem native_equivalence : nativeTheory ⊢',
 'IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding')
has('IPRACarrier65BFS943.lean','def fixedPorts : Fin 4 → ℕ :=',
 'def expression : Expr (Fin 14) := ObjectCurrentEquation2011.expressionAt (fun j => (fixedPorts j : ℤ))',
 'IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘\n      ∼mappedNativeRefutation embedding')
has('Natural79Carrier65BFSComparison.lean','(h79 : nativeTheory ⊢', '(h65 : nativeTheory ⊢',
 'native_of_endpoints Natural79EndpointDraft.native_equivalence\n    IPRACarrier65BFS943.native_equivalence',
 'IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression)')
# For h79=A↔R and h65=B↔R, these exact constructions are A→R→B and B→R→A.
has('Natural79Carrier65BFSComparison.lean',
 '(Entailment.C_trans (Entailment.K_left a) (Entailment.K_right b))',
 '(Entailment.C_trans (Entailment.K_left b) (Entailment.K_right a))')
# For z=C↔R, these exact constructions are A→R→C and C→R→A.
has('IPRABoundedRhoZFC.lean','def zfcEquiv : nativeTheory ⊢!',
 '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding')
has('Natural79Carrier65BFSComparison.lean',
 '(Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))',
 '(Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))')
has('IPRAStandardTheory.lean','theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ')
has('IPRAReferenceInductionConversion.lean','theorem nativeToReference {σ : Sentenceᵢ PRALanguage.language}',
 '(h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ')
has('IPRAOrderErasure.lean','| _, .and φ ψ => .and (erase φ) (erase ψ)',
 '| _, .imp φ ψ => .imp (erase φ) (erase ψ)')
assert draft.count('#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.')==7
assert not re.search(r'\b(?:sorry|admit|axiom|opaque|by_contra|by_cases|Classical)\b',
 '\n'.join(l for l in draft.splitlines() if not l.startswith('#print')))
print(json.dumps({'scope':'bounded pinned source signatures, direction and namespace checks; no Lean or proof closure',
 'pinned_files':len(pins),'intended_positive_shift_namespace_open':True,
 'native_comparison_directions':['A to shared target to B','B to shared target to A'],
 'translated_directions':['A to shared target to translated consistency','translated consistency to shared target to A'],
 'physical_quote_binding_checked':False,'axiom_reports_unexecuted':7,'lean_executed':False},sort_keys=True,indent=2))
