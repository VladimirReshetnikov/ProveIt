import ZFCinPA.ModelCodedBindOne
import BoundedPAConsistency.InternalRelativization

set_option autoImplicit false

/-!
Binding the same free label a second time does not alter the first bound body.
All labels, depths and formula codes are internal model elements. This syntax
lemma supplies vacuity for a later rho6 proof; it is not that numerical row.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

private instance qVecIter_delta : 𝚫₁-Function₂[V] (qVecIter L) :=
  qVecIter_defined.graph_delta.to_definable
private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

lemma termBindOneAt_absorb_any {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ chosen e : V,
    termBindOneAt L chosen e (termBindOneAt L chosen depth term) =
      termBindOneAt L chosen depth term := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz chosen e; simp
  · intro x chosen e
    classical
    by_cases h : x = chosen
    · simp [h]
    · simp [termBindOneAt_fvar, h]
  · intro arity f terms hf hv ih chosen e
    rw [termBindOneAt_func chosen depth hf hv.isUTerm,
      termBindOneAt_func chosen e hf (termBindOneVecAt_isUTerm chosen depth hv.isUTerm)]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [termBindOneVecAt_isUTerm chosen depth hv.isUTerm]
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termBindOneVecAt chosen e (termBindOneVecAt_isUTerm chosen depth hv.isUTerm) hi,
        nth_termBindOneVecAt chosen depth hv.isUTerm hi]
      exact ih i hi chosen e

lemma termBindOneAt_absorb {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ chosen : V,
    termBindOneAt L chosen (depth+1) (termBindOneAt L chosen depth term) =
      termBindOneAt L chosen depth term :=
  fun chosen => termBindOneAt_absorb_any ht chosen (depth+1)

lemma termBindOneVecAt_absorb_any {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (chosen e : V) :
    termBindOneVecAt L chosen e arity (termBindOneVecAt L chosen depth arity terms) =
      termBindOneVecAt L chosen depth arity terms := by
  apply nth_ext' arity
  · simp [termBindOneVecAt_isUTerm chosen depth ht.isUTerm]
  · simp [ht.isUTerm]
  · intro i hi
    rw [nth_termBindOneVecAt chosen e
        (termBindOneVecAt_isUTerm chosen depth ht.isUTerm) hi,
      nth_termBindOneVecAt chosen depth ht.isUTerm hi]
    exact termBindOneAt_absorb_any (ht.nth hi) chosen e

lemma termBindOneVecAt_absorb {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (chosen : V) :
    termBindOneVecAt L chosen (depth+1) arity (termBindOneVecAt L chosen depth arity terms) =
      termBindOneVecAt L chosen depth arity terms :=
  termBindOneVecAt_absorb_any ht chosen (depth+1)

/-- Once a label is bound, rebinding it at any depth leaves the body unchanged. -/
theorem bindOneAt_absorb_any {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen e : V,
    bindOneAt L chosen e (bindOneAt L chosen depth p) = bindOneAt L chosen depth p := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ chosen e : V,
    bindOneAt L chosen e (bindOneAt L chosen depth p) = bindOneAt L chosen depth p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth arity R terms hR ht chosen e
    rw [bindOneAt_rel chosen depth hR ht.isUTerm,
      bindOneAt_rel chosen e hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm)]
    rw [termBindOneVecAt_absorb_any ht chosen e]
  · intro depth arity R terms hR ht chosen e
    rw [bindOneAt_nrel chosen depth hR ht.isUTerm,
      bindOneAt_nrel chosen e hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm)]
    rw [termBindOneVecAt_absorb_any ht chosen e]
  · intro depth chosen e; simp
  · intro depth chosen e; simp
  · intro depth p q hp hq ihp ihq chosen e
    rw [bindOneAt_and chosen depth hp.isUFormula hq.isUFormula,
      bindOneAt_and chosen e (bindOneAt_isSemiformula hp chosen).isUFormula
        (bindOneAt_isSemiformula hq chosen).isUFormula, ihp chosen e, ihq chosen e]
  · intro depth p q hp hq ihp ihq chosen e
    rw [bindOneAt_or chosen depth hp.isUFormula hq.isUFormula,
      bindOneAt_or chosen e (bindOneAt_isSemiformula hp chosen).isUFormula
        (bindOneAt_isSemiformula hq chosen).isUFormula, ihp chosen e, ihq chosen e]
  · intro depth p hp ih chosen e
    rw [bindOneAt_all chosen depth hp.isUFormula,
      bindOneAt_all chosen e (bindOneAt_isSemiformula hp chosen).isUFormula, ih chosen (e+1)]
  · intro depth p hp ih chosen e
    rw [bindOneAt_exs chosen depth hp.isUFormula,
      bindOneAt_exs chosen e (bindOneAt_isSemiformula hp chosen).isUFormula, ih chosen (e+1)]

/-- Internal structural induction keeps the chosen label quantified and
increments both binder depths under each quantifier. -/
theorem bindOneAt_absorb {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen : V,
    bindOneAt L chosen (depth+1) (bindOneAt L chosen depth p) =
      bindOneAt L chosen depth p :=
  fun chosen => bindOneAt_absorb_any hp chosen (depth+1)

/-- A named universal has no remaining free occurrence of its selected label. -/
theorem bindOneAt_namedAll {p : V} (hp : IsFormula L p) (chosen : V) :
    bindOneAt L chosen 0 (namedAll L chosen p) = namedAll L chosen p := by
  rw [namedAll,bindOneAt_all chosen 0 (bindOneAt_isSemiformula hp chosen).isUFormula]
  exact congrArg (fun x : V => ^∀ x) (bindOneAt_absorb hp chosen)

/-- A substitution into a nonexistent outer slot changes nothing. The lifted
vector fixes all existing internal bound indices at each quantifier depth. -/
theorem subst_unused_free {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ x : V, subst L (qVecIter L depth (^&x ∷ 0)) p = p := by
  intro x
  apply LeanProofs.BoundedPAConsistency.InternalRelativization.subst_eq_self_of_prefix hp
    (m := depth+1) (a := depth) ?_ (by simp) (qVecIter_free_spec depth x).1
  simpa [add_comm] using qVecIter_isSemitermVec (L := L)
    (show IsSemitermVec (V := V) L 1 0 (^&x ∷ 0) by simp) depth

theorem substs1_formula {p : V} (hp : IsFormula L p) (x : V) :
    substs1 L (^&x) p = p := by
  simpa only [substs1,qVecIter_zero] using subst_unused_free hp x

/-- Opening a unary view of a formula shifts its free parameters but has no
bound slot to replace. This is used with actual shifted proof contexts. -/
theorem free_formula {p : V} (hp : IsFormula L p) :
    free L p = shift L p := by
  exact substs1_formula hp.shift 0

end LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
