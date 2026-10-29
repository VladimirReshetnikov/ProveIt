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
  · intro arity R terms hR ht a d
    rw [bindOneAt_rel a d hR ht]
    simp [hR,termBindOneVecAt_isUTerm a d ht]
  · intro arity R terms hR ht a d
    rw [bindOneAt_nrel a d hR ht]
    simp [hR,termBindOneVecAt_isUTerm a d ht]
  · intro a d; simp
  · intro a d; simp
  · intro p q hp hq ihp ihq a d
    rw [bindOneAt_and a d hp hq]
    simp [ihp a d,ihq a d]
  · intro p q hp hq ihp ihq a d
    rw [bindOneAt_or a d hp hq]
    simp [ihp a d,ihq a d]
  · intro p hp ih a d
    rw [bindOneAt_all a d hp]
    simp [ih a (d+1)]
  · intro p hp ih a d
    rw [bindOneAt_exs a d hp]
    simp [ih a (d+1)]

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
  · intro arity R terms hR ht a b d e hab
    rw [bindOneAt_rel b e hR ht,
      bindOneAt_rel a d hR (termBindOneVecAt_isUTerm b e ht),
      termBindOneVecAt_commute ht a b d e hab,
      bindOneAt_rel a d hR ht,
      bindOneAt_rel b e hR (termBindOneVecAt_isUTerm a d ht)]
  · intro arity R terms hR ht a b d e hab
    rw [bindOneAt_nrel b e hR ht,
      bindOneAt_nrel a d hR (termBindOneVecAt_isUTerm b e ht),
      termBindOneVecAt_commute ht a b d e hab,
      bindOneAt_nrel a d hR ht,
      bindOneAt_nrel b e hR (termBindOneVecAt_isUTerm a d ht)]
  · intro a b d e hab; simp
  · intro a b d e hab; simp
  · intro p q hp hq ihp ihq a b d e hab
    rw [bindOneAt_and b e hp hq,
      bindOneAt_and a d (bindOneAt_isUFormula hp b e) (bindOneAt_isUFormula hq b e),
      bindOneAt_and a d hp hq,
      bindOneAt_and b e (bindOneAt_isUFormula hp a d) (bindOneAt_isUFormula hq a d),
      ihp a b d e hab,ihq a b d e hab]
  · intro p q hp hq ihp ihq a b d e hab
    rw [bindOneAt_or b e hp hq,
      bindOneAt_or a d (bindOneAt_isUFormula hp b e) (bindOneAt_isUFormula hq b e),
      bindOneAt_or a d hp hq,
      bindOneAt_or b e (bindOneAt_isUFormula hp a d) (bindOneAt_isUFormula hq a d),
      ihp a b d e hab,ihq a b d e hab]
  · intro p hp ih a b d e hab
    rw [bindOneAt_all b e hp,
      bindOneAt_all a d (bindOneAt_isUFormula hp b (e+1)),
      bindOneAt_all a d hp,
      bindOneAt_all b e (bindOneAt_isUFormula hp a (d+1)),
      ih a b (d+1) (e+1) hab]
  · intro p hp ih a b d e hab
    rw [bindOneAt_exs b e hp,
      bindOneAt_exs a d (bindOneAt_isUFormula hp b (e+1)),
      bindOneAt_exs a d hp,
      bindOneAt_exs b e (bindOneAt_isUFormula hp a (d+1)),
      ih a b (d+1) (e+1) hab]

end LeanProofs.ZFCinPA.ModelCodedBindOneCommute
