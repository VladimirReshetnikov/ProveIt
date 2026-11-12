#!/usr/bin/env python3
"""Generate inert residual-by-residual ring bridge; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];B=D/'research/adaptive-qm36-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
a=pin(B/'AdaptiveQM36Residuals155.lean.src','03c99c18fc52e185bf8c334ce3ab62afb40c9f0d91d7bdc2cd5e695263dfae95')
b=pin(B/'AdaptiveQM36Residuals153.lean.src','05bdc1497069a2b0417b340f696cd4c69c3f84df0c97d4c5d05d5f1db01a782d')
pin(B/'AdaptiveQM36ConditionalTransfer.lean.src','865a63bdcb03a5f7dc1845bc5af0217529b3d549e7a6e67b73f0f1cf447bc754')
def vector(s):
 r=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(r)==1;return r[0].split(',')
r=vector(a);assert len(r)==27 and vector(b)==r and r[14]=='zDifference' and r[15]=='dDifference'
source='''import AdaptiveQM36Residuals153
import AdaptiveQM36ConditionalTransfer
import Mathlib.Tactic.Ring

/-! Proposed exact all-port 153↔155 ring identity and conditional endpoint.
All declarations, imports, tactics and axiom reports are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

'''
for i,n in enumerate(r):
 source+=f'''/-- Residual {i}: {n}. -/
theorem residual{i:02d} {{R : Type*}} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 36 → R) :
    (AdaptiveQM36Residuals153Draft.residuals p {i}).evalRing v =
      (AdaptiveQM36Residuals155Draft.residuals p {i}).evalRing v := by
  simp [AdaptiveQM36Residuals153Draft.residuals, AdaptiveQM36Residuals155Draft.residuals,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat] <;> ring

'''
source+='''/-- The complete positive-domain output polynomials agree over any
commutative ring, with arbitrary integer ports and every valuation. -/
theorem evaluation_identity {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 36 → R) :
    (AdaptiveQM36Literal153Draft.literal p).evalRing v =
      (AdaptiveQM36Literal155Draft.literal p).evalRing v := by
  rw [← AdaptiveQM36Residuals153Draft.sum_eq_literal,
      ← AdaptiveQM36Residuals155Draft.sum_eq_literal]
  simp only [AdaptiveQM36Residuals153Draft.sum, AdaptiveQM36Residuals155Draft.sum,
    Expr.evalRing_add, Expr.evalRing_mul]
'''
for i in range(27):source+=f'  have h{i:02d} := residual{i:02d} p v\n'
source+='  simp only ['+', '.join(f'h{i:02d}' for i in range(27))+']\n\n'
source+='''variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem internalZero_iff (p : Fin 4 → ℤ) (v : Fin 36 → V) :
    InternalZero (AdaptiveQM36Literal153Draft.literal p) v ↔
      InternalZero (AdaptiveQM36Literal155Draft.literal p) v := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    evaluation_identity p (fun i => ι (v i))]

def factored : Expr (Fin 36) :=
  AdaptiveQM36Literal153Draft.literal CurrentWindowCarry2011.ports

theorem sameNoZero : SameNoZero (positiveShift factored)
    (positiveShift AdaptiveQM36ConditionalTransferDraft.child) := by
  intro V _ _
  apply forall_congr'
  intro v
  apply not_congr
  rw [internalZero_positiveShift, internalZero_positiveShift]
  exact internalZero_iff CurrentWindowCarry2011.ports _

theorem polynomialBridge
    (h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)
    (h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)
    (h36 : AdaptiveQM36ConditionalTransferDraft.GraphZeroObligations) :
    PolynomialBridge (positiveShift factored) :=
  HAExpressionNoZeroEquiv.bridge (positiveShift factored)
    (positiveShift AdaptiveQM36ConditionalTransferDraft.child) sameNoZero
    (AdaptiveQM36ConditionalTransferDraft.polynomialBridge h38 h37 h36)

theorem native_equivalence
    (h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)
    (h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)
    (h36 : AdaptiveQM36ConditionalTransferDraft.GraphZeroObligations) : nativeTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift factored) 🡘
        ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge (positiveShift factored) (polynomialBridge h38 h37 h36)

end DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft
#print axioms DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft.evaluation_identity
#print axioms DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft.internalZero_iff
#print axioms DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft.sameNoZero
#print axioms DiophantineConsistency.AdaptiveQM36FactorizedRingBridgeDraft.native_equivalence
'''
(P/'AdaptiveQM36FactorizedRingBridge.lean.src').write_text(source)
print(json.dumps({'scope':'generated inert all-port ring identity and conditional endpoint source; no Lean','residuals':len(r),'factorized_indices':[14,15],'source_sha256':hashlib.sha256(source.encode()).hexdigest()},sort_keys=True,indent=2))
