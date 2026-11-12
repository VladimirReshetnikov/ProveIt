#!/usr/bin/env python3
"""Reconstruct two inert pointwise ring-fold bridges; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
s='''import ResidueFoldP89Residuals
import ResidueFoldFold88Residuals
import ResidueFoldP88Residuals
import ResidueFoldFold87Residuals
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import Mathlib.Tactic.Ring

/-! Two exact ring folds, composed conditionally with their respective parent
bridges. All sources and proof tactics remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.ResidueFoldsModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

section Ring
variable {R : Type*} [CommRing R]
'''
for child,parent,label in [('Fold88','P89','88_89'),('Fold87','P88','87_88')]:
 for i in range(4):
  s+=f'''theorem relation_{label}_{i} (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (ResidueFold{child}DraftResiduals.residuals p {i}).evalRing v =
      (ResidueFold{parent}DraftResiduals.residuals p {i}).evalRing v := by
  simp [ResidueFold{child}DraftResiduals.residuals,ResidueFold{parent}DraftResiduals.residuals,
    Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat] <;> ring

'''
 s+=f'''theorem evaluation_{label} (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (ResidueFold{child}Draft.literal p).evalRing v = (ResidueFold{parent}Draft.literal p).evalRing v := by
  rw [←ResidueFold{child}DraftResiduals.sum_eq_literal,←ResidueFold{parent}DraftResiduals.sum_eq_literal]
  simp only [ResidueFold{child}DraftResiduals.sum,ResidueFold{parent}DraftResiduals.sum,
    Expr.evalRing_add,Expr.evalRing_mul,relation_{label}_0 p v,relation_{label}_1 p v,
    relation_{label}_2 p v,relation_{label}_3 p v]

'''
s+='''end Ring
section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
for child,parent,label in [('Fold88','P89','88_89'),('Fold87','P88','87_88')]:
 s+=f'''theorem zero_iff_{label} (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (ResidueFold{child}Draft.literal p) v ↔
      InternalZero (ResidueFold{parent}Draft.literal p) v := by
  rw [ModelDifferenceRing.internalZero_iff,ModelDifferenceRing.internalZero_iff,
    evaluation_{label} p (fun i => ι (v i))]

theorem sameNoZero_{label} (p : Fin 4 → ℤ) : SameNoZero
    (ResidueFold{child}Draft.literal p) (ResidueFold{parent}Draft.literal p) := by
  intro V _ _
  constructor
  · intro h v hz
    exact h v ((zero_iff_{label} p v).mpr hz)
  · intro h v hz
    exact h v ((zero_iff_{label} p v).mp hz)

/-- No parent bridge is constructed or authenticated here. -/
theorem polynomialBridge_{label} (p : Fin 4 → ℤ)
    (hparent : PolynomialBridge (ResidueFold{parent}Draft.literal p)) :
    PolynomialBridge (ResidueFold{child}Draft.literal p) :=
  HAExpressionNoZeroEquiv.bridge _ _ (sameNoZero_{label} p) hparent

theorem native_equivalence_{label} (p : Fin 4 → ℤ)
    (hparent : PolynomialBridge (ResidueFold{parent}Draft.literal p)) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (ResidueFold{child}Draft.literal p) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge_{label} p hparent)

'''
s+='''end Model
end DiophantineConsistency.ResidueFoldsModelDraft
#print axioms DiophantineConsistency.ResidueFoldsModelDraft.evaluation_88_89
#print axioms DiophantineConsistency.ResidueFoldsModelDraft.evaluation_87_88
#print axioms DiophantineConsistency.ResidueFoldsModelDraft.native_equivalence_88_89
#print axioms DiophantineConsistency.ResidueFoldsModelDraft.native_equivalence_87_88
'''
t=P/'ResidueFoldsModel.lean.src'
if '--initialize' in sys.argv:t.write_text(s)
else:assert t.read_text()==s
print(json.dumps({'scope':'source reconstruction; no Lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'all_ring_residual_relations':8,'separate_parent_bridges':2},sort_keys=True,indent=2))
