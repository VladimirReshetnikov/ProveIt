import ZFCinPA.ValidatorFormulaEncoder222
import ZFCinPA.ValidatorEnvironmentSubstitution254

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Exact source substitution and opening for the actual C222 Eind encoder.
Only the unchanged term/vector/Matches helpers are reused from the syntax-only
Substitution254 leaf. The new formula identity uses actual Encoder222 equations
and explicit Pi-one structural induction under IΣ1. Total stack lookup is
preserved: no length, freshness, positivity or CProv premise is required.
This is not stream selection, semantic quantifier transport or proof translation. -/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorFormulaEncoder222
open ValidatorEnvironmentLabels254 (freeLabel freeLabel_cons_zero tail_cons)
open ValidatorEnvironmentSubstitution254 (Matches matches_qVec vec_labels_subst matches_pair)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance subst_delta : 𝚫₁-Function₂[V] (subst ℒₛₑₜ) :=
  subst.defined.graph_delta.to_definable

/-- Every dimension, source, vector and environment parameter is internal.
The source slots match total interpreted replacement lookup, not a supplied
semantic equality or provability relation. -/
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
    simp only [ValidatorFormulaEncoder222.atom,nth_adjoin_zero,nth_adjoin_one,
      vec_labels_subst ht hw he]
  · intro n arity R terms hr ht m F B B' w s hw he
    have hv := hw.termSubstVec ht
    rw [substs_nrel hr ht.isUTerm,encode_nrel F B s hr hv.isUTerm,
      encode_nrel F B' s hr ht.isUTerm]
    simp only [ValidatorFormulaEncoder222.atom,nth_adjoin_zero,nth_adjoin_one,
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

/-- Repeated interpreted labels are allowed. -/
theorem encode_subst_pair {m p t u : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (ht : IsSemiterm ℒₛₑₜ m t) (hu : IsSemiterm ℒₛₑₜ m u) (F B fresh : V) :
    encode F B fresh (subst ℒₛₑₜ (t∷u∷0) p)=
      encode F (ValidatorEnvironmentLabels254.TermLabels.term F B t∷
        ValidatorEnvironmentLabels254.TermLabels.term F B u∷0) fresh p :=
  encode_subst hp (show IsSemitermVec ℒₛₑₜ 2 m (t∷u∷0) by simp [ht,hu])
    F B _ fresh (matches_pair F B t u)

/-- The source EXS term is arbitrary internally typed syntax. Its actual
interpreted label is used, including free-environment fallback1. -/
theorem encode_substs1 {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F fresh : V) :
    encode F 0 fresh (substs1 ℒₛₑₜ t p)=
      encode F (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) fresh p := by
  have he : Matches F 0 (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) 1 (t∷0) := by
    intro i hi
    have hi0 : i=0 := by simpa using hi
    subst i
    simp
  simpa only [substs1] using encode_subst hp
    (show IsSemitermVec ℒₛₑₜ 1 0 (t∷0) by simp [ht]) F 0 _ fresh he

lemma encode_substs1_fvar {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F index fresh : V) :
    encode F 0 fresh (substs1 ℒₛₑₜ (^&index) p)=
      encode F (freeLabel F index∷0) fresh p := by
  simpa only [ValidatorEnvironmentLabels254.TermLabels.term_fvar] using
    encode_substs1 hp (show IsTerm ℒₛₑₜ (^&index) by simp) F fresh

/-- Opening first inserts the interpreted label x, then encode_shift removes
only the free-environment head. The bound slot and fresh stream are preserved. -/
lemma encode_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x fresh : V) :
    encode (x∷F) 0 fresh (free ℒₛₑₜ p)=encode F (x∷0) fresh p := by
  unfold free
  rw [encode_substs1_fvar hp.shift (x∷F) 0 fresh,freeLabel_cons_zero,
    encode_shift hp.isUFormula,tail_cons]

lemma encode_all_opened {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x : V) :
    encode F 0 x (^∀ p)=wal x (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) := by
  rw [encode_all F 0 x hp.isUFormula,encode_free hp F x (x+2)]

lemma encode_exs_opened {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x : V) :
    encode F 0 x (^∃ p)=wim (wal x (wim (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) 1)) 1 := by
  rw [encode_exs F 0 x hp.isUFormula,encode_free hp F x (x+2)]

end LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution222
