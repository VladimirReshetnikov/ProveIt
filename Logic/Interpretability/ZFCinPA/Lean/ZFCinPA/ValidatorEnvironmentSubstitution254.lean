import ZFCinPA.ValidatorEnvironmentLabels254

set_option autoImplicit false
noncomputable section

/-!
Exact encoding under an arbitrary internal simultaneous substitution vector.
Its source slots are interpreted by a pointwise bound-environment relation.
The same binder label is pushed on both sides. This is a syntax identity,
with no CProv, freshness, alpha-conversion or native-axiom assertion.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open ValidatorEnvironmentLabels254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each original bound slot has the interpreted label of its replacement.
Lengths of the label environments are unnecessary for this syntax identity. -/
def Matches (F B B' n w : V) : Prop :=
  ∀ i<n, TermLabels.term F B w.[i]=B'.[i]

lemma term_labels_bShift {n t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (F B label : V) :
    TermLabels.term F (label∷B) (termBShift ℒₛₑₜ t)=TermLabels.term F B t := by
  rcases ht.case with (⟨i,_hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · simp
  · simp
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

lemma matches_qVec {n m F B B' w : V}
    (hw : IsSemitermVec ℒₛₑₜ n m w) (he : Matches F B B' n w) (label : V) :
    Matches F (label∷B) (label∷B') (n+1) (qVec ℒₛₑₜ w) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simp [Bootstrapping.qVec]
  · have hin : i<n := by simpa using hi
    simp only [Bootstrapping.qVec,nth_adjoin_succ,hw.lh]
    rw [nth_termBShiftVec hw.isUTerm hin,term_labels_bShift (hw.nth hin) F B label]
    exact he i hin

lemma term_labels_subst {n t F B B' w : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (he : Matches F B B' n w) :
    TermLabels.term F B (termSubst ℒₛₑₜ w t)=TermLabels.term F B' t := by
  rcases ht.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [termSubst_bvar,TermLabels.term_bvar]
    exact he i hi
  · simp
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

lemma vec_labels_subst {n m arity terms F B B' w : V}
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (hw : IsSemitermVec ℒₛₑₜ n m w)
    (he : Matches F B B' n w) :
    TermLabels.vec F B arity (termSubstVec ℒₛₑₜ arity w terms)=
      TermLabels.vec F B' arity terms := by
  have hv := hw.termSubstVec ht
  apply nth_ext' arity
  · exact TermLabels.vec_length F B hv.isUTerm
  · exact TermLabels.vec_length F B' ht.isUTerm
  · intro i hi
    rw [TermLabels.vec_nth F B hv.isUTerm hi,nth_termSubstVec ht.isUTerm hi,
      TermLabels.vec_nth F B' ht.isUTerm hi]
    exact term_labels_subst (ht.nth hi) he

private instance subst_delta : 𝚫₁-Function₂[V] (subst ℒₛₑₜ) :=
  subst.defined.graph_delta.to_definable

/-- All dimensions, source codes, vectors and indices range internally. -/
theorem encode_subst {n m p w : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (hw : IsSemitermVec ℒₛₑₜ n m w) (F B B' fresh : V)
    (he : Matches F B B' n w) :
    encode F B fresh (subst ℒₛₑₜ w p)=encode F B' fresh p := by
  refine (IsSemiformula.pi1_structural_induction (P := fun n p =>
    ∀ m F B B' w s : V, IsSemitermVec ℒₛₑₜ n m w → Matches F B B' n w →
      encode F B s (subst ℒₛₑₜ w p)=encode F B' s p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp) m F B B' w fresh hw he
  · unfold Matches; definability
  · intro n arity R terms hr ht m F B B' w s hw he
    have hv := hw.termSubstVec ht
    rw [substs_rel hr ht.isUTerm,encode_rel F B s hr hv.isUTerm,
      encode_rel F B' s hr ht.isUTerm]
    simp only [ValidatorEnvironmentLabels254.Formulas.atom,nth_adjoin_zero,nth_adjoin_one,
      vec_labels_subst ht hw he]
  · intro n arity R terms hr ht m F B B' w s hw he
    have hv := hw.termSubstVec ht
    rw [substs_nrel hr ht.isUTerm,encode_nrel F B s hr hv.isUTerm,
      encode_nrel F B' s hr ht.isUTerm]
    simp only [ValidatorEnvironmentLabels254.Formulas.atom,nth_adjoin_zero,nth_adjoin_one,
      vec_labels_subst ht hw he]
  · intro n m F B B' w s hw he; simp
  · intro n m F B B' w s hw he; simp
  · intro n p q hp hq ihp ihq m F B B' w s hw he
    rw [substs_and hp.isUFormula hq.isUFormula,
      encode_and F B s (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      encode_and F B' s hp.isUFormula hq.isUFormula,
      ihp m F B B' w s hw he,ihq m F B B' w s hw he]
  · intro n p q hp hq ihp ihq m F B B' w s hw he
    rw [substs_or hp.isUFormula hq.isUFormula,
      encode_or F B s (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      encode_or F B' s hp.isUFormula hq.isUFormula,
      ihp m F B B' w s hw he,ihq m F B B' w s hw he]
  · intro n p hp ih m F B B' w s hw he
    rw [substs_all hp.isUFormula,encode_all F B s (hp.subst hw.qVec).isUFormula,
      encode_all F B' s hp.isUFormula,
      ih (m+1) F (s∷B) (s∷B') (qVec ℒₛₑₜ w) (s+2) hw.qVec (matches_qVec hw he s)]
  · intro n p hp ih m F B B' w s hw he
    rw [substs_ex hp.isUFormula,encode_exs F B s (hp.subst hw.qVec).isUFormula,
      encode_exs F B' s hp.isUFormula,
      ih (m+1) F (s∷B) (s∷B') (qVec ℒₛₑₜ w) (s+2) hw.qVec (matches_qVec hw he s)]

lemma matches_pair (F B t u : V) :
    Matches F B (TermLabels.term F B t∷TermLabels.term F B u∷0) 2 (t∷u∷0) := by
  intro i hi
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with (rfl | rfl)
  · simp
  · simp

/-- Two source slots may be replaced simultaneously, even when their labels coincide. -/
theorem encode_subst_pair {m p t u : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (ht : IsSemiterm ℒₛₑₜ m t) (hu : IsSemiterm ℒₛₑₜ m u) (F B fresh : V) :
    encode F B fresh (subst ℒₛₑₜ (t∷u∷0) p)=
      encode F (TermLabels.term F B t∷TermLabels.term F B u∷0) fresh p :=
  encode_subst hp (show IsSemitermVec ℒₛₑₜ 2 m (t∷u∷0) by simp [ht,hu])
    F B _ fresh (matches_pair F B t u)

/-- The two bound-slot orders needed in the NativeGic skeleton. -/
theorem encode_subst_two_bvars {m p i j : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (hi : i<m) (hj : j<m) (F B fresh : V) :
    encode F B fresh (subst ℒₛₑₜ (^#i∷^#j∷0) p)=
      encode F (B.[i]∷B.[j]∷0) fresh p := by
  simpa only [TermLabels.term_bvar] using encode_subst_pair hp
    (show IsSemiterm ℒₛₑₜ m (^#i) by simpa using hi)
    (show IsSemiterm ℒₛₑₜ m (^#j) by simpa using hj) F B fresh

/-- Simultaneous instantiation by free variables, including fallback labels. -/
theorem encode_subst_two_fvars {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (F B fresh i j : V) :
    encode F B fresh (subst ℒₛₑₜ (^&i∷^&j∷0) p)=
      encode F (freeLabel F i∷freeLabel F j∷0) fresh p := by
  simpa only [TermLabels.term_fvar] using encode_subst_pair hp
    (show IsSemiterm ℒₛₑₜ 0 (^&i) by simp)
    (show IsSemiterm ℒₛₑₜ 0 (^&j) by simp) F B fresh

end LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254
