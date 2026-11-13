#!/usr/bin/env python3
"""Reconstruct inert 90↔positive-82 valuation transport; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
s='''import Residue82Residuals
import Residue90FyForce
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import Mathlib.Tactic.Ring

/-! Proposed direct 90/positive-82 model bridge; no Lean elaboration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.Residue90To82TransportDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open Residue90CompactPortBoundsDraft

def Forced (i : Fin 13) : Prop := i=0 ∨ i=3 ∨ i=6 ∨ i=11 ∨ i=12
instance (i : Fin 13) : Decidable (Forced i) := by unfold Forced; infer_instance

def mixed {V : Type*} [Add V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if Forced i then v i else v i+1

def lower {V : Type*} [Sub V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if Forced i then v i else v i-1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mixed_pos (v : Fin 13 → V) (h : ∀ i, Forced i → 0<v i) : ∀ i, 0<mixed v i := by
  intro i
  unfold mixed
  split
  · exact h i ‹Forced i›
  · exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)

theorem mixed_lower (v : Fin 13 → V) (h : ∀ i, 0<v i) : mixed (lower v)=v := by
  funext i
  by_cases hi : Forced i
  · simp [mixed,lower,hi]
  · simp [mixed,lower,hi,tsub_add_cancel_of_le (pos_iff_one_le.mp (h i))]

/-- Composition of the five prior source-only graph forcing declarations. -/
theorem forced_pos (K : ℕ) (v : Fin 13 → V)
    (hz : InternalZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) v) :
    ∀ i, Forced i → 0<v i := by
  have hJ := Residue90FirstNormJDraft.J_positive (ports K) v hz
  have hX := Residue90XZeroGraphDraft.compact_X_positive K v hz
  have hfy := Residue90FyForceDraft.f_y_positive (ports K) v hz
  have hg := Residue90XZeroGraphDraft.compact_gamma_positive K v hz
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact hJ
  · exact hfy.1
  · exact hX
  · exact hfy.2
  · exact hg

'''
for i in range(4):
 s+=f'''theorem relation{i:02d} (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue90ResidualsDraft.residuals p {i}).evalRing (fun k => ι (v k)) =
      (Residue82ResidualsDraft.residuals p {i}).evalRing (fun k => ι (mixed v k)) := by
  simp [Residue90ResidualsDraft.residuals,Residue82ResidualsDraft.residuals,
    mixed,Forced,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> ring

'''
s+='''theorem evaluation (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue90LiteralDraft.literal p).evalRing (fun k => ι (v k)) =
      (Residue82LiteralDraft.literal p).evalRing (fun k => ι (mixed v k)) := by
  rw [←Residue90ResidualsDraft.sum_eq_literal,←Residue82ResidualsDraft.sum_eq_literal]
  simp only [Residue90ResidualsDraft.sum,Residue82ResidualsDraft.sum,
    Expr.evalRing_add,Expr.evalRing_mul,relation00 p v,relation01 p v,relation02 p v,relation03 p v]

theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (Residue90LiteralDraft.literal p) v ↔
      InternalZero (Residue82LiteralDraft.literal p) (mixed v) := by
  rw [ModelDifferenceRing.internalZero_iff,ModelDifferenceRing.internalZero_iff,evaluation p v]

theorem compact_no_zero_iff (K : ℕ) :
    (∀ v : Fin 13 → V, ¬InternalZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) v) ↔
      ∀ v : Fin 13 → V, ¬InternalZero (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ)))) v := by
  constructor
  · intro h v hz
    let old : Fin 13 → V := fun i => v i+1
    have hp : ∀ i,0<old i := fun i => lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hzero : InternalZero (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ))) old :=
      (internalZero_positiveShift _ _).mp hz
    have hlift : mixed (lower old)=old := mixed_lower old hp
    apply h (lower old)
    apply (zero_iff _ (lower old)).mpr
    simpa only [hlift] using hzero
  · intro h v hz
    have hv := mixed_pos v (forced_pos K v hz)
    let shifted : Fin 13 → V := fun i => mixed v i-1
    have hs : (fun i => shifted i+1)=mixed v := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv i))
    apply h shifted
    rw [internalZero_positiveShift,hs]
    exact (zero_iff _ v).mp hz

theorem compact_sameNoZero (K : ℕ) : SameNoZero
    (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ)))
    (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ)))) := by
  intro V _ _
  exact compact_no_zero_iff (V:=V) K

/-- The positive-82 parent bridge remains a separate explicit hypothesis. -/
theorem polynomialBridge (K : ℕ)
    (hparent : PolynomialBridge (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ))))) :
    PolynomialBridge (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) :=
  HAExpressionNoZeroEquiv.bridge _ _ (compact_sameNoZero K) hparent

theorem native_equivalence (K : ℕ)
    (hparent : PolynomialBridge (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ))))) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge K hparent)
end DiophantineConsistency.Residue90To82TransportDraft
#print axioms DiophantineConsistency.Residue90To82TransportDraft.forced_pos
#print axioms DiophantineConsistency.Residue90To82TransportDraft.compact_no_zero_iff
#print axioms DiophantineConsistency.Residue90To82TransportDraft.native_equivalence
'''
t=P/'Residue90To82Transport.lean.src'
if '--initialize' in sys.argv:t.write_text(s)
else:assert t.read_text()==s
print(json.dumps({'scope':'source transport reconstruction, no Lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'residual_relations':4,'forced_indices':[0,3,6,11,12]},sort_keys=True,indent=2))
