import ZFCinPA.ModelCodedBindOneCommute
import ZFCinPA.ModelCodedBindOne
import ZFCinPA.ModelCodedBindTwoSlots

set_option autoImplicit false

/-!
Internal exchange of two distinct named binders. The existing arbitrary bound
depth is retained, while the two new bound slots are swapped by a represented
qVec iteration. Every label, depth and matrix code is internal; no finite
standard support or closed-matrix premise occurs. Equal labels are intentionally
excluded from this swap identity and handled separately by numerical clients.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def swapVec (L : Language) [L.Encodable] [L.LORDefinable]
    (depth : V) : V := qVecIter L depth (^#1 ∷ ^#0 ∷ 0)
noncomputable def swapVecDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out depth.
      ∃ b0, !qqBvarDef b0 0 ∧ ∃ b1, !qqBvarDef b1 1 ∧
      ∃ v0, !adjoinDef v0 b0 0 ∧ ∃ v, !adjoinDef v b1 v0 ∧
      !(qVecIterDef L) out depth v”
instance swapVec_defined : 𝚺₁-Function₁[V] (swapVec L) via swapVecDef L :=
  .mk fun e => by simp [swapVecDef,swapVec]
private instance swapVec_delta : 𝚫₁-Function₁[V] (swapVec L) :=
  swapVec_defined.graph_delta.to_definable
private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance termBindOneVecAt_delta : 𝚫₁-Function₄[V] (termBindOneVecAt L) :=
  termBindOneVecAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

@[simp] lemma swapVec_zero : swapVec (V := V) L 0 = ^#1 ∷ ^#0 ∷ 0 := by
  simp [swapVec]
lemma swapVec_succ (depth : V) : swapVec L (depth+1) = qVec L (swapVec L depth) := by
  simp [swapVec]
lemma swapVec_isSemitermVec (depth : V) :
    IsSemitermVec L (depth+2) (depth+2) (swapVec L depth) := by
  simpa only [swapVec,add_comm] using qVecIter_isSemitermVec (L := L)
    (show IsSemitermVec (V := V) L 2 2 (^#1 ∷ ^#0 ∷ 0) by simp) depth

lemma swapVec_spec (depth : V) :
    (∀ i < depth, (swapVec L depth).[i] = ^#i) ∧
    (swapVec L depth).[depth] = ^#(depth+1) ∧
    (swapVec L depth).[depth+1] = ^#depth := by
  simpa only [swapVec, ModelCodedBindTwoSlots.twoSlotVec, add_zero] using
    (ModelCodedBindTwoSlots.twoSlotVec_spec (L := L) (1 : V) 0 depth)

lemma termBindOneAt_swap {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ a b : V, a ≠ b →
    termSubst L (swapVec L depth)
      (termBindOneAt L a (depth+1) (termBindOneAt L b depth term)) =
      termBindOneAt L b (depth+1) (termBindOneAt L a depth term) := by
  intro a b hab
  have h := ModelCodedBindTwoSlots.termBindTwo_reindex ht b a (1 : V) 0 hab.symm
  rw [add_zero, ModelCodedBindOneCommute.termBindOneAt_commute ht.isUTerm a b depth (depth+1) hab] at h
  simpa only [swapVec,ModelCodedBindTwoSlots.twoSlotVec,add_zero] using h

lemma termBindOneVecAt_swap {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (a b : V) (hab : a ≠ b) :
    termSubstVec L arity (swapVec L depth)
      (termBindOneVecAt L a (depth+1) arity (termBindOneVecAt L b depth arity terms)) =
      termBindOneVecAt L b (depth+1) arity (termBindOneVecAt L a depth arity terms) := by
  have h := ModelCodedBindTwoSlots.termBindTwoVec_reindex ht b a (1 : V) 0 hab.symm
  rw [add_zero, ModelCodedBindOneCommute.termBindOneVecAt_commute ht.isUTerm a b depth (depth+1) hab] at h
  simpa only [swapVec,ModelCodedBindTwoSlots.twoSlotVec,add_zero] using h

lemma bindOneAt_swap {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ a b : V, a ≠ b →
    subst L (swapVec L depth) (bindOneAt L a (depth+1) (bindOneAt L b depth p)) =
      bindOneAt L b (depth+1) (bindOneAt L a depth p) := by
  intro a b hab
  have h := ModelCodedBindTwoSlots.bindTwo_reindex hp b a (1 : V) 0 hab.symm
  rw [add_zero, ModelCodedBindOneCommute.bindOneAt_commute hp.isUFormula a b depth (depth+1) hab] at h
  simpa only [swapVec,ModelCodedBindTwoSlots.twoSlotVec,add_zero] using h

end LeanProofs.ZFCinPA.ModelCodedBindOneSwap
