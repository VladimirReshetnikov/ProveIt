import ZFCinPA.ModelCodedBindOne

set_option autoImplicit false

/-!
Named-binder compatibility with negation and implication, uniformly over
internal formulas, labels and existing bound depths. The formula induction
retains the selected label, while its internal depth changes under binders.
These syntax laws do not assert numerical axiom-row provability.
-/
namespace LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

lemma bindOneAt_neg {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen : V,
    bindOneAt L chosen depth (neg L p) = neg L (bindOneAt L chosen depth p) := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ chosen : V,
    bindOneAt L chosen depth (neg L p) = neg L (bindOneAt L chosen depth p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth arity R terms hR ht chosen
    simp [hR,ht.isUTerm,bindOneAt_rel,bindOneAt_nrel,termBindOneVecAt_isUTerm]
  · intro depth arity R terms hR ht chosen
    simp [hR,ht.isUTerm,bindOneAt_rel,bindOneAt_nrel,termBindOneVecAt_isUTerm]
  · intro depth chosen; simp
  · intro depth chosen; simp
  · intro depth p q hp hq ihp ihq chosen
    simp [hp.isUFormula,hq.isUFormula,hp.isUFormula.neg,hq.isUFormula.neg,
      bindOneAt_and,bindOneAt_or,
      (bindOneAt_isSemiformula hp chosen).isUFormula,
      (bindOneAt_isSemiformula hq chosen).isUFormula,ihp chosen,ihq chosen]
  · intro depth p q hp hq ihp ihq chosen
    simp [hp.isUFormula,hq.isUFormula,hp.isUFormula.neg,hq.isUFormula.neg,
      bindOneAt_and,bindOneAt_or,
      (bindOneAt_isSemiformula hp chosen).isUFormula,
      (bindOneAt_isSemiformula hq chosen).isUFormula,ihp chosen,ihq chosen]
  · intro depth p hp ih chosen
    simp [hp.isUFormula,hp.isUFormula.neg,bindOneAt_all,bindOneAt_exs,
      (bindOneAt_isSemiformula hp chosen).isUFormula,ih chosen]
  · intro depth p hp ih chosen
    simp [hp.isUFormula,hp.isUFormula.neg,bindOneAt_all,bindOneAt_exs,
      (bindOneAt_isSemiformula hp chosen).isUFormula,ih chosen]

lemma bindOneAt_imp {depth p q : V}
    (hp : IsSemiformula L depth p) (hq : IsSemiformula L depth q) (chosen : V) :
    bindOneAt L chosen depth (imp L p q) =
      imp L (bindOneAt L chosen depth p) (bindOneAt L chosen depth q) := by
  unfold imp
  rw [bindOneAt_or chosen depth hp.isUFormula.neg hq.isUFormula,
    bindOneAt_neg hp chosen]

end LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
