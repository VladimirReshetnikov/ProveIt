import ZFCinPA.ModelCodedBindOne

set_option autoImplicit false

/-! Commutation of binding distinct free labels in internal syntax. -/
namespace LeanProofs.ZFCinPA.ModelCodedBindOneCommute
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

lemma bindOneAt_isUFormula {p : V} (hp : IsUFormula L p) :
    ∀ chosen depth : V, IsUFormula L (bindOneAt L chosen depth p) := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [bindOneAt_rel, bindOneAt_nrel, bindOneAt_and, bindOneAt_or,
      bindOneAt_all, bindOneAt_exs, termBindOneVecAt_isUTerm]

/-- Binding different free labels commutes when each keeps its own depth.
This is raw syntax; no claim swaps two quantified slots without substitution. -/
lemma termBindOneAt_commute {term : V} (ht : IsUTerm L term) :
    ∀ a b d e : V, a ≠ b →
    termBindOneAt L a d (termBindOneAt L b e term) =
      termBindOneAt L b e (termBindOneAt L a d term) := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z a b d e hab; simp
  · intro x a b d e hab
    classical
    by_cases ha : x = a
    · subst x
      simp [termBindOneAt_fvar,hab]
    · by_cases hb : x = b
      · subst x
        simp [termBindOneAt_fvar,hab.symm]
      · simp [termBindOneAt_fvar,ha,hb]
  · intro arity f terms hf hv ih a b d e hab
    rw [termBindOneAt_func b e hf hv,
      termBindOneAt_func a d hf (termBindOneVecAt_isUTerm b e hv),
      termBindOneAt_func a d hf hv,
      termBindOneAt_func b e hf (termBindOneVecAt_isUTerm a d hv)]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [termBindOneVecAt_isUTerm b e hv]
    · simp [termBindOneVecAt_isUTerm a d hv]
    · intro i hi
      rw [nth_termBindOneVecAt a d (termBindOneVecAt_isUTerm b e hv) hi,
        nth_termBindOneVecAt b e hv hi,
        nth_termBindOneVecAt b e (termBindOneVecAt_isUTerm a d hv) hi,
        nth_termBindOneVecAt a d hv hi]
      exact ih i hi a b d e hab

lemma termBindOneVecAt_commute {arity terms : V} (ht : IsUTermVec L arity terms)
    (a b d e : V) (hab : a ≠ b) :
    termBindOneVecAt L a d arity (termBindOneVecAt L b e arity terms) =
      termBindOneVecAt L b e arity (termBindOneVecAt L a d arity terms) := by
  apply nth_ext' arity
  · simp [termBindOneVecAt_isUTerm b e ht]
  · simp [termBindOneVecAt_isUTerm a d ht]
  · intro i hi
    rw [nth_termBindOneVecAt a d (termBindOneVecAt_isUTerm b e ht) hi,
      nth_termBindOneVecAt b e ht hi,
      nth_termBindOneVecAt b e (termBindOneVecAt_isUTerm a d ht) hi,
      nth_termBindOneVecAt a d ht hi]
    exact termBindOneAt_commute (ht.nth hi) a b d e hab

lemma bindOneAt_commute {p : V} (hp : IsUFormula L p) :
    ∀ a b d e : V, a ≠ b →
    bindOneAt L a d (bindOneAt L b e p) =
      bindOneAt L b e (bindOneAt L a d p) := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [bindOneAt_rel, bindOneAt_nrel, bindOneAt_and, bindOneAt_or,
      bindOneAt_all, bindOneAt_exs, termBindOneVecAt_isUTerm,
      bindOneAt_isUFormula] <;> aesop (add safe termBindOneVecAt_commute)

end LeanProofs.ZFCinPA.ModelCodedBindOneCommute
