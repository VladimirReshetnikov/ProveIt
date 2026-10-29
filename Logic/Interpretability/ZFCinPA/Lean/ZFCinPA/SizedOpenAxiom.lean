import ZFCinPA.SizedSchemaLeaves
import ZFCinPA.ModelCodedOpenSchemaAxioms

/-!
# Bounded open schema axioms

`ModelCodedOpenSchemaAxioms.openAxiomProofCode p` is an *explicit* internal
proof of an open schema instance `p`. It starts from the axiom
`closeFormulaCode p = ∀^m (bindFreeAt 0 p)` and applies `specializeCode`
`m` times, through the iterator `specializedProofCode`. This module bounds
that code.

* `specializeCode_le`: one specialization costs three levels.
* `spc_le`: the iteration, by Π₁ induction on the remaining binders. Every
  intermediate body is a *fixed* body under one substitution `W` of variable
  terms. The step composes `W` with the next opening vector
  (`termSubstVec v W` is again a vector of variable terms), so levels never
  compound.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedOpenAxiom

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation LeanProofs.BoundedPAConsistency.SubstBound
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SizedCongruence LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms LeanProofs.ZFCinPA.ModelCodedBindFree

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Bound variables are below the code -/

theorem termBV_le {t : V} (ht : IsUTerm ℒₛₑₜ t) : termBV ℒₛₑₜ t ≤ t := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [termBV_bvar]
    exact _root_.add_le_add (le_pair_right _ _) le_rfl
  · rw [termBV_fvar]; exact Arithmetic.zero_le _

theorem vec_le_rel (tag k R v : V) : v ≤ ⟪tag, k, R, v⟫ + 1 :=
  le_trans (le_pair_right R _) (le_trans (le_pair_right k _) (le_trans (le_pair_right tag _) le_self_add))

theorem bv_le_self {p : V} (hp : IsUFormula ℒₛₑₜ p) : bv ℒₛₑₜ p ≤ p := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (P := fun p => bv ℒₛₑₜ p ≤ p) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k R v hR hv
    rw [bv_rel hR hv]
    refine listMaxss_le fun i hi => ?_
    have hik : i < k := by simpa [len_termBVVec hv] using hi
    rw [nth_termBVVec hv hik]
    exact le_trans (termBV_le (hv.nth hik)) (le_trans (le_of_lt (nth_lt_self (by simpa [hv.lh] using hik)))
      (vec_le_rel 0 k R v))
  · intro k R v hR hv
    rw [bv_nrel hR hv]
    refine listMaxss_le fun i hi => ?_
    have hik : i < k := by simpa [len_termBVVec hv] using hi
    rw [nth_termBVVec hv hik]
    exact le_trans (termBV_le (hv.nth hik)) (le_trans (le_of_lt (nth_lt_self (by simpa [hv.lh] using hik)))
      (vec_le_rel 1 k R v))
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [bv_and hp hq]
    exact max_le (le_trans ihp (le_of_lt (lt_K!_left p q))) (le_trans ihq (le_of_lt (lt_K!_right p q)))
  · intro p q hp hq ihp ihq
    rw [bv_or hp hq]
    exact max_le (le_trans ihp (le_of_lt (lt_or_left p q))) (le_trans ihq (le_of_lt (lt_or_right p q)))
  · intro p hp ih
    rw [bv_all hp]
    exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_forall p)))
  · intro p hp ih
    rw [bv_ex hp]
    exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_exists p)))

/-! ## Universal prefixes cost one level per binder -/

theorem qqAlls_level {b ℓ : V} (hℓ : 2 ≤ ℓ) (hb : b ≤ lvB ℓ) :
    ∀ k : V, qqAlls b k ≤ lvB (ℓ + 2 * k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · simp only [lvB]; definability
  · simpa using hb
  · case succ k ih =>
    rw [qqAlls_succ]
    have h2 : (2 : V) ≤ ℓ + 2 * k := le_trans hℓ le_self_add
    have := pair_lvB h2 (tag_le_lvB (k := 6) (by norm_num) h2) ih
    refine le_trans this (lvB_mono (le_of_eq ?_))
    ring

/-! ## One specialization -/

/-- **`specializeCode`, bounded**: three levels. -/
theorem specializeCode_le {proof body term w : V} (hw : 4 ≤ w)
    (hproof : proof ≤ Exp.exp (lvB w))
    (h₁ : substs1 ℒₛₑₜ term body < lvB w) (h₂ : ^∀ body < lvB w)
    (h₃ : neg ℒₛₑₜ (^∀ body) < lvB w) (h₄ : substs1 ℒₛₑₜ term (neg ℒₛₑₜ body) < lvB w)
    (h₅ : neg ℒₛₑₜ body < lvB w) (h₆ : term < lvB w) :
    specializeCode ℒₛₑₜ proof body term ≤ Exp.exp (lvB (w + 1 + 1 + 1)) := by
  have he := four_le_lvB' hw
  have e1 : Exp.exp (1024 * lvB w) ≤ Exp.exp (lvB (w + 1)) := step_le hw
  have hw1 : 4 ≤ w + 1 := le_trans hw le_self_add
  have hw2 : 4 ≤ w + 1 + 1 := le_trans hw1 le_self_add
  have e2 : Exp.exp (1024 * lvB (w + 1)) ≤ Exp.exp (lvB (w + 1 + 1)) := step_le hw1
  have e3 : Exp.exp (1024 * lvB (w + 1 + 1)) ≤ Exp.exp (lvB (w + 1 + 1 + 1)) := step_le hw2
  have up : ∀ {x : V}, x ≤ Exp.exp (lvB w) → ∀ k : V, w ≤ k → x ≤ Exp.exp (lvB k) :=
    fun hx k hk => le_trans hx (exp_monotone_le.mpr (lvB_mono hk))
  have lexp : ∀ {x : V}, x < lvB w → x ≤ Exp.exp (lvB w) :=
    fun hx => le_trans (le_of_lt hx) (le_of_lt (lt_exp _))
  -- the sequents
  set result := substs1 ℒₛₑₜ term body
  set s := insert result (0 : V)
  set leftS := insert (^∀ body) s
  set rightS := insert (neg ℒₛₑₜ (^∀ body)) s
  set emS := insert (substs1 ℒₛₑₜ term (neg ℒₛₑₜ body)) rightS
  have hs : s ≤ Exp.exp (lvB w) := DerivableLe.seq_le le_rfl
    (DerivableLe.insert_lt h₁ (fun y hy => by simp [emptyset_def] at hy))
  have hsS : ∀ y ∈ s, y < lvB w := DerivableLe.insert_lt h₁ (fun y hy => by simp at hy)
  have hleftS : leftS ≤ Exp.exp (lvB w) := DerivableLe.seq_le le_rfl (DerivableLe.insert_lt h₂ hsS)
  have hrightS : rightS ≤ Exp.exp (lvB w) := DerivableLe.seq_le le_rfl (DerivableLe.insert_lt h₃ hsS)
  have hemS : emS ≤ Exp.exp (lvB w) :=
    DerivableLe.seq_le le_rfl (DerivableLe.insert_lt h₄ (DerivableLe.insert_lt h₃ hsS))
  have dax : axL emS result ≤ Exp.exp (lvB (w + 1)) := le_trans (axL_le he hemS (lexp h₁)) e1
  have dex : exsIntro rightS (neg ℒₛₑₜ body) term (axL emS result) ≤ Exp.exp (lvB (w + 1 + 1)) :=
    le_trans (exsIntro_le (four_le_lvB' hw1) (up hrightS _ le_self_add) (up (lexp h₅) _ le_self_add)
      (up (lexp h₆) _ le_self_add) dax) e2
  have dwk : wkRule leftS proof ≤ Exp.exp (lvB (w + 1 + 1)) :=
    le_trans (le_trans (wkRule_le he hleftS hproof) e1)
      (exp_monotone_le.mpr (lvB_mono le_self_add))
  have hup2 : ∀ {x : V}, x ≤ Exp.exp (lvB w) → x ≤ Exp.exp (lvB (w + 1 + 1)) :=
    fun hx => up hx _ (le_trans le_self_add le_self_add)
  exact le_trans (cutRule_le (four_le_lvB' hw2) (hup2 hs) (hup2 (lexp h₂)) dwk dex) e3

/-! ## The iterator, one binder at a time -/

theorem spc_zero (body proof : V) : specializedProofCode ℒₛₑₜ 0 body proof = proof := by
  simp [specializedProofCode]

theorem spc_succ {r body proof : V} (hb : IsSemiformula ℒₛₑₜ (r + 1) body) :
    specializedProofCode ℒₛₑₜ (r + 1) body proof =
      specializedProofCode ℒₛₑₜ r (subst ℒₛₑₜ (qVecIter ℒₛₑₜ r (^&r ∷ 0)) body)
        (specializeCode ℒₛₑₜ proof (qqAlls body r) (^&r)) := by
  have hnext : substs1 ℒₛₑₜ (^&r) (qqAlls body r) =
      qqAlls (subst ℒₛₑₜ (qVecIter ℒₛₑₜ r (^&r ∷ 0)) body) r :=
    subst_qqAlls r 1 0 body (^&r ∷ 0) (by simpa [add_comm] using hb) (by simp)
  have hstate : advance ℒₛₑₜ ⟪r + 1, qqAlls body (r + 1), proof⟫ =
      ⟪r, qqAlls (subst ℒₛₑₜ (qVecIter ℒₛₑₜ r (^&r ∷ 0)) body) r,
        specializeCode ℒₛₑₜ proof (qqAlls body r) (^&r)⟫ := by
    simp [advance, qqAlls_succ, qqAll, sndIdx, hnext]
  unfold specializedProofCode
  rw [runState_succ_left, hstate]

/-- The member level of the specialization chain. -/
def spcW (l₀ c R : V) : V := 10 * (10 * (l₀ + 1) + c + 2 * R + 3) + 10

set_option maxHeartbeats 4000000 in
/-- **The specialization iterator, bounded**: `r` binders cost `3r` levels
above `spcW`, for every body of the form `subst W body₀` with `W` a vector
of variable terms at level `c`. -/
theorem spc_le {body₀ n₀ l₀ c R : V} (hb₀ : IsSemiformula ℒₛₑₜ n₀ body₀) (hl₀ : body₀ ≤ lvB l₀)
    (hc : 1 ≤ c) (hvar : ∀ z ≤ R, (^#z : V) ≤ lvB c ∧ (^&z : V) ≤ lvB c) :
    ∀ r : V, r ≤ R → ∀ W proof w : V, IsSemitermVec ℒₛₑₜ n₀ r W →
      (∀ i < n₀, W.[i] ≤ lvB c ∧ IsVarTerm W.[i]) → proof ≤ Exp.exp (lvB w) → spcW l₀ c R ≤ w →
      specializedProofCode ℒₛₑₜ r (subst ℒₛₑₜ W body₀) proof ≤ Exp.exp (lvB (w + 3 * r)) := by
  intro r
  induction r using ISigma1.pi1_succ_induction
  · simp only [lvB, IsVarTerm, spcW]
    definability
  · intro _ W proof w _ _ hp _
    simpa [spc_zero] using hp
  · case succ r ih =>
    intro hrR W proof w hW hWb hp hw
    have hr : r ≤ R := le_trans le_self_add hrR
    have hbody : IsSemiformula ℒₛₑₜ (r + 1) (subst ℒₛₑₜ W body₀) := hb₀.subst hW
    rw [spc_succ hbody]
    set v := qVecIter ℒₛₑₜ r (^&r ∷ 0) with hvd
    have hv : IsSemitermVec ℒₛₑₜ (r + 1) r v := by
      simpa [hvd, add_comm] using qVecIter_isSemitermVec (L := ℒₛₑₜ)
        (show IsSemitermVec (V := V) ℒₛₑₜ 1 0 (^&r ∷ 0) by simp) r
    have hcomp : subst ℒₛₑₜ v (subst ℒₛₑₜ W body₀) = subst ℒₛₑₜ (termSubstVec ℒₛₑₜ n₀ v W) body₀ :=
      Bootstrapping.substs_substs hb₀ hv hW
    rw [hcomp]
    have hW' : IsSemitermVec ℒₛₑₜ n₀ r (termSubstVec ℒₛₑₜ n₀ v W) := hv.termSubstVec hW
    have hspec := qVecIter_free_spec (L := ℒₛₑₜ) r r
    have hW'b : ∀ i < n₀, (termSubstVec ℒₛₑₜ n₀ v W).[i] ≤ lvB c ∧
        IsVarTerm (termSubstVec ℒₛₑₜ n₀ v W).[i] := by
      intro i hi
      rw [nth_termSubstVec hW.isUTerm hi]
      have hti := hW.nth hi
      rcases term_var hti.isUTerm with ⟨z, hz⟩ | ⟨x, hx⟩
      · have hzr : z < r + 1 := by simpa [hz] using hti
        rw [hz, termSubst_bvar]
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hzr) with hzr' | rfl
        · rw [hspec.1 z hzr']
          exact ⟨(hvar z (le_trans (le_of_lt hzr') hr)).1, isVarTerm_bvar z⟩
        · rw [hspec.2]
          exact ⟨(hvar z hr).2, closed_isVar (by simp)⟩
      · rw [hx, termSubst_fvar]
        have := hWb i hi
        rw [hx] at this
        exact this
    -- levels of the chain's formulas
    set S := 10 * (l₀ + 1) + c with hS
    have hS2 : (2 : V) ≤ S := two_le_m l₀ c
    have lB : subst ℒₛₑₜ W body₀ ≤ lvB S :=
      subst_level l₀ body₀ hl₀ hb₀.isUFormula c n₀ (r + 1) W hc hW (fun i hi => (hWb i hi).1)
        (fun i hi => (hWb i hi).2)
    have lB' : subst ℒₛₑₜ (termSubstVec ℒₛₑₜ n₀ v W) body₀ ≤ lvB S :=
      subst_level l₀ body₀ hl₀ hb₀.isUFormula c n₀ r _ hc hW' (fun i hi => (hW'b i hi).1)
        (fun i hi => (hW'b i hi).2)
    have lQ := qqAlls_level hS2 lB r
    have lQ1 := qqAlls_level hS2 lB (r + 1)
    have lQ' := qqAlls_level hS2 lB' r
    have hR2 : ∀ j ≤ R + 1, S + 2 * j ≤ S + 2 * R + 2 := fun j hj => by
      rw [show S + 2 * R + 2 = S + 2 * (R + 1) by ring]
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hj (by norm_num))
    set M := S + 2 * R + 2 with hM
    have hMw : 10 * (M + 1) + 1 ≤ w := by
      refine le_trans ?_ hw
      unfold spcW
      rw [hM, hS]
      exact le_of_add_eq (y := 9) (by ring)
    have hMM : M ≤ 10 * (M + 1) := le_trans (le_self_add : M ≤ M + 1)
      (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num : (1 : V) ≤ 10))
    have hcS : c ≤ S := by rw [hS]; exact le_add_self
    have hSM : S ≤ M := by rw [hM]; exact le_trans le_self_add le_self_add
    have hall : ^∀ (qqAlls (subst ℒₛₑₜ W body₀) r) = qqAlls (subst ℒₛₑₜ W body₀) (r + 1) :=
      (qqAlls_succ _ _).symm
    have fQ : IsSemiformula ℒₛₑₜ 1 (qqAlls (subst ℒₛₑₜ W body₀) r) :=
      IsSemiformula.qqAlls (by simpa [add_comm] using hbody)
    have hnext : substs1 ℒₛₑₜ (^&r) (qqAlls (subst ℒₛₑₜ W body₀) r) =
        qqAlls (subst ℒₛₑₜ (termSubstVec ℒₛₑₜ n₀ v W) body₀) r := by
      rw [← hcomp]
      exact subst_qqAlls r 1 0 _ (^&r ∷ 0) (by simpa [add_comm] using hbody) (by simp)
    have lt1 : ∀ {x j : V}, x ≤ lvB (S + 2 * j) → j ≤ R + 1 → x < lvB w := fun hx hj =>
      lt_of_le_of_lt (lift_lvB hx (le_trans (hR2 _ hj) hMM))
        (lt_of_lt_of_le (lt_lvB_succ le_rfl) (lvB_mono hMw))
    have ltn : ∀ {x j : V}, x ≤ lvB (S + 2 * j) → j ≤ R + 1 → IsUFormula ℒₛₑₜ x →
        neg ℒₛₑₜ x < lvB w := fun hx hj hxF =>
      lt_of_le_of_lt (lift_lvB (neg_level _ _ hx hxF)
        (mul_le_mul_of_nonneg_left (_root_.add_le_add (hR2 _ hj) le_rfl) (by norm_num)))
        (lt_of_lt_of_le (lt_lvB_succ le_rfl) (lvB_mono hMw))
    have hr1 : r ≤ R + 1 := le_trans hr le_self_add
    have hr1' : r + 1 ≤ R + 1 := _root_.add_le_add hr le_rfl
    have fQ1 : IsUFormula ℒₛₑₜ (qqAlls (subst ℒₛₑₜ W body₀) (r + 1)) :=
      isUFormula_qqAlls.mpr hbody.isUFormula
    have fQ' : IsUFormula ℒₛₑₜ (qqAlls (subst ℒₛₑₜ (termSubstVec ℒₛₑₜ n₀ v W) body₀) r) :=
      isUFormula_qqAlls.mpr (hb₀.subst hW').isUFormula
    have hspc := specializeCode_le (le_trans (le_of_add_eq (y := 10 * M + 7) (by ring)) hMw)
      hp (by rw [hnext]; exact lt1 lQ' hr1) (by rw [hall]; exact lt1 lQ1 hr1')
      (by rw [hall]; exact ltn lQ1 hr1' fQ1)
      (by
        rw [show substs1 ℒₛₑₜ (^&r) (neg ℒₛₑₜ (qqAlls (subst ℒₛₑₜ W body₀) r)) =
            neg ℒₛₑₜ (substs1 ℒₛₑₜ (^&r) (qqAlls (subst ℒₛₑₜ W body₀) r)) from
          Bootstrapping.substs_neg fQ (by simp : IsSemitermVec ℒₛₑₜ 1 0 (^&r ∷ 0 : V)), hnext]
        exact ltn lQ' hr1 fQ')
      (ltn lQ hr1 fQ.isUFormula)
      (lt_of_le_of_lt (lift_lvB (hvar r hr).2 (le_trans hcS (le_trans hSM hMM)))
        (lt_of_lt_of_le (lt_lvB_succ le_rfl) (lvB_mono hMw)))
    have ih' := ih hr (termSubstVec ℒₛₑₜ n₀ v W) _ (w + 1 + 1 + 1) hW' hW'b hspc
      (le_trans hw (le_trans le_self_add (le_trans le_self_add le_self_add)))
    rw [show w + 1 + 1 + 1 + 3 * r = w + 3 * (r + 1) by ring] at ih'
    exact ih'

end LeanProofs.ZFCinPA.SizedOpenAxiom
