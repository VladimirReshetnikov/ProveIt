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
open LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms

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
  have atom_bound (tag k R v : V) (hv : IsUTermVec ℒₛₑₜ k v) :
      listMax (termBVVec ℒₛₑₜ k v) ≤ ⟪tag, k, R, v⟫ + 1 := by
    refine listMaxss_le fun i hi => ?_
    have hik : i < k := by simpa [len_termBVVec hv] using hi
    rw [nth_termBVVec hv hik]
    exact le_trans (termBV_le (hv.nth hik)) (le_trans (le_of_lt (nth_lt_self (by simpa [hv.lh] using hik)))
      (vec_le_rel tag k R v))
  refine IsUFormula.ISigma1.sigma1_succ_induction (P := fun p => bv ℒₛₑₜ p ≤ p) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k R v hR hv
    rw [bv_rel hR hv]
    exact atom_bound 0 k R v hv
  · intro k R v hR hv
    rw [bv_nrel hR hv]
    exact atom_bound 1 k R v hv
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
    have body_level {depth vector : V} (hvec : IsSemitermVec ℒₛₑₜ n₀ depth vector)
        (hentries : ∀ i < n₀, vector.[i] ≤ lvB c ∧ IsVarTerm vector.[i]) :
        subst ℒₛₑₜ vector body₀ ≤ lvB S :=
      subst_level l₀ body₀ hl₀ hb₀.isUFormula c n₀ depth vector hc hvec
        (fun i hi => (hentries i hi).1) (fun i hi => (hentries i hi).2)
    have lB := body_level hW hWb
    have lB' := body_level hW' hW'b
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
    have below : ∀ {x level : V}, x ≤ lvB level → level ≤ 10 * (M + 1) → x < lvB w :=
      fun hx hlevel => lt_of_le_of_lt (lift_lvB hx hlevel)
        (lt_of_lt_of_le (lt_lvB_succ le_rfl) (lvB_mono hMw))
    have lt1 : ∀ {x j : V}, x ≤ lvB (S + 2 * j) → j ≤ R + 1 → x < lvB w := fun hx hj =>
      below hx (le_trans (hR2 _ hj) hMM)
    have ltn : ∀ {x j : V}, x ≤ lvB (S + 2 * j) → j ≤ R + 1 → IsUFormula ℒₛₑₜ x →
        neg ℒₛₑₜ x < lvB w := fun hx hj hxF =>
      below (neg_level _ _ hx hxF)
        (mul_le_mul_of_nonneg_left (_root_.add_le_add (hR2 _ hj) le_rfl) (by norm_num))
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
      (below (hvar r hr).2 (le_trans hcS (le_trans hSM hMM)))
    have ih' := ih hr (termSubstVec ℒₛₑₜ n₀ v W) _ (w + 1 + 1 + 1) hW' hW'b hspc
      (le_trans hw (le_trans le_self_add (le_trans le_self_add le_self_add)))
    rw [show w + 1 + 1 + 1 + 3 * r = w + 3 * (r + 1) by ring] at ih'
    exact ih'

/-! ## Closing a formula: `bindFreeAt` levels -/

theorem vec2_bindFree (d : V) {a b : V} (ha : IsUTerm ℒₛₑₜ a) (hb : IsUTerm ℒₛₑₜ b) :
    termBindFreeVecAt ℒₛₑₜ d 2 (a ∷ b ∷ 0) =
      termBindFreeAt ℒₛₑₜ d a ∷ termBindFreeAt ℒₛₑₜ d b ∷ 0 := by
  have hv : IsUTermVec ℒₛₑₜ 2 (a ∷ b ∷ 0 : V) := by simp [ha, hb]
  apply nth_ext' 2 (by rw [termBindFreeVecAt_lh d hv]) (by simp [one_add_one_eq_two])
  intro i hi
  rw [nth_termBindFreeVecAt d hv hi]
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl <;> simp

theorem two_le_lvB (y : V) : 2 ≤ lvB y := by
  have := lvB_mono (Arithmetic.zero_le y); rwa [lvB_zero] at this

theorem two_mul_lvB_le (y : V) : lvB y + lvB y ≤ lvB (y + 1) := by
  rw [lvB_succ, ← two_mul]
  exact mul_le_mul_of_nonneg_right (two_le_lvB y) (Arithmetic.zero_le _)

theorem tbf_le {d t u C : V} (hC : 2 ≤ C) (ht : IsUTerm ℒₛₑₜ t) (htu : t ≤ lvB u)
    (hd : d ≤ lvB C) : termBindFreeAt ℒₛₑₜ d t ≤ lvB (u + C + 3) := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [termBindFreeAt_bvar]
    exact lift_lvB htu (le_trans le_self_add le_self_add)
  · rw [termBindFreeAt_fvar]
    have hx : x ≤ lvB u := le_trans (le_trans (le_pair_right _ _) le_self_add) htu
    have hs : d + x ≤ lvB (u + C + 1) :=
      le_trans (_root_.add_le_add (lift_lvB hd (le_add_self : C ≤ u + C))
        (lift_lvB hx (le_self_add : u ≤ u + C))) (two_mul_lvB_le (u + C))
    have h2 : (2 : V) ≤ u + C + 1 := le_trans hC (le_trans (le_add_self : C ≤ u + C) le_self_add)
    have := pair_lvB h2 (Arithmetic.zero_le (lvB (u + C + 1))) hs
    have e : u + C + 1 + 2 = u + C + 3 := by ring
    rw [e] at this
    exact this

set_option maxHeartbeats 4000000 in
/-- **`bindFreeAt` multiplies levels**, under the invariant `depth + level ≤ D`. -/
theorem bindFreeAt_level {C D : V} (hC : 2 ≤ C) (hD : D ≤ lvB C) :
    ∀ u x : V, x ≤ lvB u → IsUFormula ℒₛₑₜ x → ∀ d : V, d + u ≤ D →
      bindFreeAt ℒₛₑₜ d x ≤ lvB (10 * (u + 1) + C + 13) := by
  intro u
  induction u using ISigma1.pi1_succ_induction
  · simp only [lvB]
    definability
  · intro x hx hxF
    exact absurd rfl (formula_level_pos hx hxF)
  · case succ u ih =>
    intro x hx hxF d hdD
    have hd : d ≤ lvB C := le_trans (le_trans le_self_add hdD) hD
    have hdu : d + u ≤ D := le_trans (_root_.add_le_add le_rfl le_self_add) hdD
    have hdu1 : d + 1 + u ≤ D := by rw [add_assoc, add_comm 1 u]; exact hdD
    set m := 10 * (u + 1) + C + 13 with hm
    have hm2 : (2 : V) ≤ m := le_trans hC (le_trans (le_add_self : C ≤ 10 * (u + 1) + C) le_self_add)
    have hfin : m + 10 = 10 * (u + 1 + 1) + C + 13 := by rw [hm]; ring
    have hatom : u + C + 3 + 10 ≤ 10 * (u + 1 + 1) + C + 13 :=
      le_of_add_eq (y := 9 * u + 20) (by ring)
    have hC3 : (2 : V) ≤ u + C + 3 := le_trans hC (le_trans (le_add_self : C ≤ u + C) le_self_add)
    have atom_case (tag k R v : V) (htag : tag ≤ 1) (hR : Language.IsRel ℒₛₑₜ k R)
        (hv : IsUTermVec ℒₛₑₜ k v) (hx : ⟪tag, k, R, v⟫ + 1 ≤ lvB (u + 1)) :
        ⟪tag, k, R, termBindFreeVecAt ℒₛₑₜ d k v⟫ + 1 ≤
          lvB (10 * (u + 1 + 1) + C + 13) := by
      obtain ⟨rfl, hR01⟩ := isRel_set hR
      obtain ⟨t₁, t₂, rfl, ht₁, ht₂⟩ := vec_two hv
      rw [vec2_bindFree d ht₁ ht₂]
      obtain ⟨h₁, h₂⟩ := atom_children hx
      have hR1 : R ≤ 1 := by rcases hR01 with rfl | rfl <;> simp
      exact lift_lvB (atom_rebuild hC3 htag hR1 (tbf_le hC ht₁ h₁ hd) (tbf_le hC ht₂ h₂ hd)) hatom
    have binary_case (tag p q : V) (htag : tag ≤ 16)
        (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q)
        (hx : ⟪tag, ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1)) :
        ⟪tag, ⟪bindFreeAt ℒₛₑₜ d p, bindFreeAt ℒₛₑₜ d q⟫⟫ + 1 ≤
          lvB (10 * (u + 1 + 1) + C + 13) := by
      have hY := (pair_children hx).2
      have ihp := ih p (le_trans (le_pair_left _ _) hY) hp d hdu
      have ihq := ih q (le_trans (le_pair_right _ _) hY) hq d hdu
      rw [← hfin]
      exact pair_lvB_le (le_trans hm2 le_self_add) (slack4 _)
        (tag_le_lvB htag (le_trans hm2 le_self_add)) (pair_lvB' hm2 ihp ihq)
    have binder_case (tag p : V) (htag : tag ≤ 16) (hp : IsUFormula ℒₛₑₜ p)
        (hx : ⟪tag, p⟫ + 1 ≤ lvB (u + 1)) :
        ⟪tag, bindFreeAt ℒₛₑₜ (d + 1) p⟫ + 1 ≤ lvB (10 * (u + 1 + 1) + C + 13) := by
      have ihp := ih p (pair_children hx).2 hp (d + 1) hdu1
      rw [← hfin]
      exact lift_lvB (pair_lvB hm2 (tag_le_lvB htag hm2) ihp)
        (_root_.add_le_add le_rfl (by norm_num))
    rcases hxF.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
        ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [bindFreeAt_rel d hR hv]
      exact atom_case 0 k R v (by simp) hR hv hx
    · rw [bindFreeAt_nrel d hR hv]
      exact atom_case 1 k R v le_rfl hR hv hx
    · rw [bindFreeAt_verum]
      exact lift_lvB hx (le_of_add_eq (y := 9 * u + 32 + C) (by ring))
    · rw [bindFreeAt_falsum]
      exact lift_lvB hx (le_of_add_eq (y := 9 * u + 32 + C) (by ring))
    · rw [bindFreeAt_and d hp hq]
      exact binary_case 4 p q (by norm_num) hp hq hx
    · rw [bindFreeAt_or d hp hq]
      exact binary_case 5 p q (by norm_num) hp hq hx
    · rw [bindFreeAt_all d hp]
      exact binder_case 6 p (by norm_num) hp hx
    · rw [bindFreeAt_exs d hp]
      exact binder_case 7 p (by norm_num) hp hx

/-! ## The identity vector of bound variables -/

theorem bvarId_semitermVec (m : V) : IsSemitermVec ℒₛₑₜ m m (qVecIter ℒₛₑₜ m 0) := by
  simpa using qVecIter_isSemitermVec (L := ℒₛₑₜ) (show IsSemitermVec (V := V) ℒₛₑₜ 0 0 0 by simp) m

theorem bvarId_nth : ∀ m : V, ∀ i < m, (qVecIter ℒₛₑₜ m 0).[i] = ^#i :=
  fun m => qVecIter_prefix (show IsSemitermVec (V := V) ℒₛₑₜ 0 0 0 by simp) m

/-! ## The bounded open axiom -/

/-- The level of the closed body `bindFreeAt 0 q`, for `q` at level `u`. -/
def openL (u : V) : V := 10 * (u + 1) + u + 13

/-- **The level of a bounded open schema axiom proof.** -/
def openW (u : V) : V :=
  spcW (openL u) (openL u + 2) (lvB (openL u)) + 3 * lvB (openL u)

set_option maxHeartbeats 2000000 in
/-- **Open schema axioms, bounded.** If the universal closure of `q` is a
`𝗭𝗙` axiom, then `q` itself, at level `u`, has a `𝗭𝗙`-derivation at level
`openW u`: the explicit `openAxiomProofCode q`. -/
theorem open_axiom_le {q u : V} (hq : IsFormula ℒₛₑₜ q) (hqu : q ≤ lvB u) (hu : 2 ≤ u)
    (hclosed : closeFormulaCode ℒₛₑₜ q ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    DLv 𝗭𝗙 (insert q ∅) (openW u) := by
  set b := bindFreeAt ℒₛₑₜ 0 q with hbdef
  obtain ⟨hbU, -, -⟩ := bindFreeAt_closing hq
  set m := bv ℒₛₑₜ b with hmdef
  have hbm : IsSemiformula ℒₛₑₜ m b := ⟨hbU, le_rfl⟩
  set l₀ := openL u with hl₀
  have lb : b ≤ lvB l₀ := bindFreeAt_level hu (le_lvB_self u) u q hqu hq.isUFormula 0 (by simp)
  have hm : m ≤ lvB l₀ := le_trans (bv_le_self hbU) lb
  have hl2 : (2 : V) ≤ l₀ := le_trans hu (le_trans (le_add_self : u ≤ 10 * (u + 1) + u) le_self_add)
  set c := l₀ + 2 with hc
  have hc1 : (1 : V) ≤ c := le_trans (by norm_num) (le_add_self : (2 : V) ≤ l₀ + 2)
  have hvar : ∀ z ≤ m, (^#z : V) ≤ lvB c ∧ (^&z : V) ≤ lvB c := fun z hz => by
    have hz' : z ≤ lvB l₀ := le_trans hz hm
    exact ⟨pair_lvB hl2 (Arithmetic.zero_le _) hz',
      pair_lvB hl2 (le_trans (by norm_num) (two_le_lvB l₀)) hz'⟩
  have hι := bvarId_semitermVec (V := V) m
  have hιb : ∀ i < m, (qVecIter ℒₛₑₜ m 0).[i] ≤ lvB c ∧ IsVarTerm (qVecIter ℒₛₑₜ m 0).[i] :=
    fun i hi => by
      rw [bvarId_nth m i hi]
      exact ⟨(hvar i (le_of_lt hi)).1, isVarTerm_bvar i⟩
  have hsubst : subst ℒₛₑₜ (qVecIter ℒₛₑₜ m 0) b = b :=
    Bootstrapping.subst_eq_self hbm hι (bvarId_nth m)
  -- the axiom node
  set A := closeFormulaCode ℒₛₑₜ q with hA
  have hAq : A = qqAlls b m := rfl
  have lA : A ≤ lvB (l₀ + 2 * m) := hAq ▸ qqAlls_level hl2 lb m
  have hw4 : (4 : V) ≤ l₀ + 2 * m + 1 :=
    le_trans (le_of_add_eq (y := 10 * u + u + 19) (by rw [hl₀]; unfold openL; ring))
      (le_trans le_self_add le_self_add)
  have hAe : A < lvB (l₀ + 2 * m + 1) := lt_lvB_succ lA
  have hP0 : axiomCode A ≤ Exp.exp (lvB (spcW l₀ c m)) := by
    have hax := axm_le (four_le_lvB' hw4)
      (DerivableLe.seq_le le_rfl (DerivableLe.insert_lt hAe (fun y (hy : y ∈ (∅ : V)) => by simp at hy)))
      (le_trans (le_of_lt hAe) (le_of_lt (lt_exp _)))
    refine le_trans hax (le_trans (step_le hw4) (exp_monotone_le.mpr (lvB_mono ?_)))
    exact le_of_add_eq (y := 99 * l₀ + 18 * m + 10 * c + 138) (by unfold spcW; ring)
  have hspc := spc_le hbm lb hc1 hvar m le_rfl _ _ _ hι hιb hP0 le_rfl
  rw [hsubst] at hspc
  have hcode : openAxiomProofCode ℒₛₑₜ q = specializedProofCode ℒₛₑₜ m b (axiomCode A) := rfl
  have hproof := openAxiomProofCode_isProof (𝗭𝗙 : SetTheory) hq hclosed
  refine ⟨openAxiomProofCode ℒₛₑₜ q, ?_, by rw [← singleton_eq_insert]; exact hproof⟩
  rw [hcode]
  refine le_trans hspc (exp_monotone_le.mpr (lvB_mono ?_))
  unfold openW spcW
  rw [← hl₀, ← hc]
  exact _root_.add_le_add (_root_.add_le_add (mul_le_mul_of_nonneg_left
    (_root_.add_le_add (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (by norm_num))) le_rfl)
    (by norm_num)) le_rfl) (mul_le_mul_of_nonneg_left hm (by norm_num))

/-- **Open separation instances, bounded.** -/
theorem open_sep_le (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) {u : V}
    (hK : (sepBody K).val ≤ lvB u) (hu : 2 ≤ u) :
    DLv 𝗭𝗙 (insert (sepBody K).val ∅) (openW u) :=
  open_axiom_le (sepBody K).isSemiformula hK hu
    (by simpa only [closedSeparation, ← sepBodyVal_eq K] using closedSeparation_mem_zf K)

/-- **Open replacement instances, bounded.** -/
theorem open_rep_le (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) {u : V}
    (hK : (repBody K).val ≤ lvB u) (hu : 2 ≤ u) :
    DLv 𝗭𝗙 (insert (repBody K).val ∅) (openW u) :=
  open_axiom_le (repBody K).isSemiformula hK hu
    (by simpa only [closedReplacement, ← repBodyVal_eq K] using closedReplacement_mem_zf K)

end LeanProofs.ZFCinPA.SizedOpenAxiom
