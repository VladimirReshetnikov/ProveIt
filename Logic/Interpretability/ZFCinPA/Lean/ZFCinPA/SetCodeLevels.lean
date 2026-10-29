import ZFCinPA.SetRelativization
import BoundedPAConsistency.ShiftBound
import BoundedPAConsistency.SubstBound

/-!
# Code levels for `ℒₛₑₜ` formulas: syntax operations multiply levels

Write `lvB u = 2^(2^u)`; a code `x` has *level* `u` when `x ≤ lvB u`. In every
model of `𝗜𝚺₁`, for internal `ℒₛₑₜ` formulas:

* `shift_level`: shifting raises the level by one;
* `neg_level`: negation sends level `u` to level `10·(u+1)`;
* `subst_level`: substituting variable terms with entries at level `c₀`
  sends level `u` to level `10·(u+1) + c₀`.

These are the *iteration-friendly* bounds. A construction that repeats such
an operation `j` times (the matching codes `mVal j`, for instance) stays at
level `C·16^j`, a fixed-height tower in `j`. The cruder value bounds of
`SubstBound` (double exponential in the code itself) would compound into a
tower of height growing with `j`.

The proofs are inductions on the level `u`, not on formula structure. A
Cantor pair at least squares each of its entries (`sq_le_pair_left/right`),
so the immediate subformulas of a level-`(u+1)` code have level `u`, and
rebuilding a node with at most five pairings costs at most `+10` levels
(`pair_lvB`). No `ℒₛₑₜ` formula has code below `3`, so level `0` is vacuous.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SetCodeLevels

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound
open LeanProofs.BoundedPAConsistency.ShiftBound
open LeanProofs.BoundedPAConsistency.SubstBound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Levels -/

section Levels

/-- The level bound `2^(2^u)`. -/
def lvB (u : V) : V := Exp.exp (Exp.exp u)

theorem lvB_succ (u : V) : lvB (u + 1) = lvB u * lvB u := by
  unfold lvB
  rw [exp_succ, exp_even, sq]

theorem lvB_mono {u v : V} (h : u ≤ v) : lvB u ≤ lvB v := exp_exp_mono h

theorem le_lvB_self (u : V) : u ≤ lvB u := self_le_exp_exp u

theorem lvB_one : lvB (1 : V) = 4 := by
  unfold lvB
  rw [exp_one, exp_two]

theorem four_le_lvB {u : V} (hu : 1 ≤ u) : 4 ≤ lvB u := by
  rw [← lvB_one]
  exact lvB_mono hu

theorem le_lvB_of_sq {a u : V} (h : a * a ≤ lvB (u + 1)) : a ≤ lvB u := by
  by_contra hc
  have hlt : lvB u < a := not_le.mp hc
  rw [lvB_succ] at h
  exact absurd h (not_le.mpr (mul_lt_mul'' hlt hlt (Arithmetic.zero_le _) (Arithmetic.zero_le _)))

theorem sq_le_pair_left (a b : V) : a * a ≤ ⟪a, b⟫ := by
  simp only [pair]
  split_ifs with h
  · exact le_trans (mul_le_mul (le_of_lt h) (le_of_lt h) (Arithmetic.zero_le _)
      (Arithmetic.zero_le _)) le_self_add
  · rw [add_assoc]
    exact le_self_add

theorem sq_le_pair_right (a b : V) : b * b ≤ ⟪a, b⟫ := by
  simp only [pair]
  split_ifs with h
  · exact le_self_add
  · have hb : b ≤ a := not_lt.mp h
    refine le_trans (mul_le_mul hb hb (Arithmetic.zero_le _) (Arithmetic.zero_le _)) ?_
    rw [add_assoc]
    exact le_self_add

/-- The entries of a pair one level up sit one level down. -/
theorem pair_children {a b u : V} (h : ⟪a, b⟫ + 1 ≤ lvB (u + 1)) :
    a ≤ lvB u ∧ b ≤ lvB u :=
  ⟨le_lvB_of_sq (le_trans (sq_le_pair_left a b) (le_trans le_self_add h)),
    le_lvB_of_sq (le_trans (sq_le_pair_right a b) (le_trans le_self_add h))⟩

/-- **One pairing costs two levels** (above level `2`). -/
theorem pair_lvB {a b u : V} (hu : 2 ≤ u) (ha : a ≤ lvB u) (hb : b ≤ lvB u) :
    ⟪a, b⟫ + 1 ≤ lvB (u + 2) := by
  have he : (3 : V) ≤ Exp.exp u :=
    le_trans (by norm_num) (le_trans (le_of_eq exp_two.symm) (exp_monotone_le.mpr hu))
  refine le_trans (pair_succ_le_exp he ha hb) ?_
  unfold lvB
  refine exp_monotone_le.mpr (le_of_eq ?_)
  rw [exp_add, exp_two]
  ring

theorem pair_lvB' {a b u : V} (hu : 2 ≤ u) (ha : a ≤ lvB u) (hb : b ≤ lvB u) :
    ⟪a, b⟫ ≤ lvB (u + 2) :=
  le_trans le_self_add (pair_lvB hu ha hb)

end Levels

/-! ## The shape of `ℒₛₑₜ` syntax -/

section Shape

theorem isRel_set {k R : V} (hR : (ℒₛₑₜ).IsRel k R) : k = 2 ∧ (R = 0 ∨ R = 1) := by
  have hr' : V ⊧/![k, R] (LeanProofs.ZFCinPA.instLORDefinableSet.rel).val := hR
  rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.rel : 𝚺₀.Semisentence 2) =
    .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” from rfl] at hr'
  have hc : (k = 2 ∧ R = 0) ∨ (k = 2 ∧ R = 1) := by simpa using hr'
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, Or.inl h2⟩
  · exact ⟨h1, Or.inr h2⟩

/-- `ℒₛₑₜ` terms are variables. -/
theorem term_var {t : V} (ht : IsUTerm ℒₛₑₜ t) : (∃ z, t = ^#z) ∨ (∃ x, t = ^&x) := by
  rcases ht.case with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, -, rfl⟩
  · exact Or.inl ⟨z, rfl⟩
  · exact Or.inr ⟨x, rfl⟩
  · exact absurd hf (SetRelativization.set_not_isFunc k f)

/-- A vector of two terms is `?[v.[0], v.[1]]`. -/
theorem vec_two {v : V} (hv : IsUTermVec ℒₛₑₜ 2 v) :
    ∃ t₁ t₂, v = t₁ ∷ t₂ ∷ 0 ∧ IsUTerm ℒₛₑₜ t₁ ∧ IsUTerm ℒₛₑₜ t₂ := by
  have hl : len v = 2 := hv.1.symm
  rcases adjoin_cases v with rfl | ⟨t₁, v₁, rfl⟩
  · simp at hl
  rcases adjoin_cases v₁ with rfl | ⟨t₂, v₂, rfl⟩
  · simp at hl
  rcases adjoin_cases v₂ with rfl | ⟨t₃, v₃, rfl⟩
  · refine ⟨t₁, t₂, rfl, by simpa using hv.2 0 (by simp), by simpa using hv.2 1 (by simp)⟩
  · exfalso
    simp only [len_adjoin] at hl
    have : len v₃ + 1 + 1 + 1 = 0 + 1 + 1 := by rw [hl]; norm_num
    simp at this

/-- No `ℒₛₑₜ` formula has code below `3`. -/
theorem three_le_formula {x : V} (hx : IsUFormula ℒₛₑₜ x) : 3 ≤ x := by
  have tagged : ∀ t Y : V, 2 ≤ t → 3 ≤ ⟪t, Y⟫ + 1 := fun t Y ht => by
    have := sq_le_pair_left t Y
    have h4 : (4 : V) ≤ t * t := le_trans (by norm_num : (4 : V) ≤ 2 * 2)
      (mul_le_mul ht ht (Arithmetic.zero_le _) (Arithmetic.zero_le _))
    exact le_trans (by norm_num : (3 : V) ≤ 4) (le_trans h4 (le_trans this le_self_add))
  have atomic : ∀ t R v : V, 3 ≤ ⟪t, ⟪2, ⟪R, v⟫⟫⟫ + 1 := fun t R v => by
    have h1 := sq_le_pair_right t ⟪2, ⟪R, v⟫⟫
    have h2 := sq_le_pair_left 2 ⟪R, v⟫
    have h4 : (4 : V) ≤ ⟪2, ⟪R, v⟫⟫ := le_trans (by norm_num) h2
    have h16 : (3 : V) ≤ ⟪2, ⟪R, v⟫⟫ * ⟪2, ⟪R, v⟫⟫ :=
      le_trans (by norm_num : (3 : V) ≤ 4 * 4) (mul_le_mul h4 h4 (Arithmetic.zero_le _)
        (Arithmetic.zero_le _))
    exact le_trans h16 (le_trans h1 le_self_add)
  rcases hx.case with ⟨k, R, v, hR, -, rfl⟩ | ⟨k, R, v, hR, -, rfl⟩ | rfl | rfl |
      ⟨p, q, -, -, rfl⟩ | ⟨p, q, -, -, rfl⟩ | ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩
  · obtain ⟨rfl, -⟩ := isRel_set hR
    exact atomic 0 R v
  · obtain ⟨rfl, -⟩ := isRel_set hR
    exact atomic 1 R v
  · exact tagged 2 0 (by norm_num)
  · exact tagged 3 0 (by norm_num)
  · exact tagged 4 _ (by norm_num)
  · exact tagged 5 _ (by norm_num)
  · exact tagged 6 _ (by norm_num)
  · exact tagged 7 _ (by norm_num)

end Shape

/-! ## The level bounds -/

section Main

theorem lvB_zero : lvB (0 : V) = 2 := by
  unfold lvB
  rw [exp_zero, exp_one]

theorem formula_level_pos {x u : V} (hx : x ≤ lvB u) (hxF : IsUFormula ℒₛₑₜ x) : u ≠ 0 := by
  rintro rfl
  rw [lvB_zero] at hx
  exact absurd (le_trans (three_le_formula hxF) hx) (by norm_num)

/-- **Shifting raises the level by one.** -/
theorem shift_level {x u : V} (hx : x ≤ lvB u) : shift ℒₛₑₜ x ≤ lvB (u + 1) := by
  rw [lvB_succ]
  exact le_trans (shift_le_sq x) (mul_le_mul hx hx (Arithmetic.zero_le _) (Arithmetic.zero_le _))

theorem termSubst_var_le {w t ℓ c₀ u : V} (hl : len w = ℓ) (hwb : ∀ i < ℓ, w.[i] ≤ lvB c₀)
    (ht : IsUTerm ℒₛₑₜ t) (htu : t ≤ lvB u) : termSubst ℒₛₑₜ w t ≤ lvB (u + c₀) := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [termSubst_bvar]
    by_cases hz : z < ℓ
    · exact le_trans (hwb z hz) (lvB_mono le_add_self)
    · rw [nth_lt_len (by rw [hl]; exact not_lt.mp hz)]
      exact Arithmetic.zero_le _
  · rw [termSubst_fvar]
    exact le_trans htu (lvB_mono le_self_add)

theorem lift_lvB {x a b : V} (hx : x ≤ lvB a) (h : a ≤ b) : x ≤ lvB b := le_trans hx (lvB_mono h)

theorem two_le_m (u c₀ : V) : (2 : V) ≤ 10 * (u + 1) + c₀ :=
  le_trans (by norm_num : (2 : V) ≤ 10) (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _)
    le_add_self) le_self_add)

/-- Rebuilding an atom `⟪t, 2, R, a ∷ b ∷ 0⟫ + 1` from entries at level `m`. -/
theorem atom_rebuild {t R a b m : V} (hm : 2 ≤ m) (ht : t ≤ 1) (hR : R ≤ 1) (ha : a ≤ lvB m)
    (hb : b ≤ lvB m) : ⟪t, 2, R, a ∷ b ∷ 0⟫ + 1 ≤ lvB (m + 10) := by
  have h1 : (1 : V) ≤ lvB m := le_trans (by norm_num) (four_le_lvB (le_trans (by norm_num) hm))
  have h2 : (2 : V) ≤ lvB m := le_trans (by norm_num) (four_le_lvB (le_trans (by norm_num) hm))
  simp only [adjoin_def]
  have s1 := pair_lvB hm hb (Arithmetic.zero_le (lvB m))
  have s2 := pair_lvB (le_trans hm le_self_add) (lift_lvB ha le_self_add) s1
  have s3 := pair_lvB' (le_trans hm (le_trans le_self_add le_self_add))
    (lift_lvB (le_trans hR h1) (le_trans le_self_add le_self_add)) s2
  have s4 := pair_lvB' (le_trans hm (le_trans le_self_add (le_trans le_self_add le_self_add)))
    (lift_lvB h2 (le_trans le_self_add (le_trans le_self_add le_self_add))) s3
  have s5 := pair_lvB (le_trans hm (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add le_self_add))))
    (lift_lvB (le_trans ht h1) (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add le_self_add)))) s4
  refine le_trans s5 (lvB_mono (le_of_eq ?_))
  ring

/-- The children of a level-`(u+1)` atom. -/
theorem atom_children {t R a b u : V} (hx : ⟪t, 2, R, a ∷ b ∷ 0⟫ + 1 ≤ lvB (u + 1)) :
    a ≤ lvB u ∧ b ≤ lvB u := by
  have hY := (pair_children hx).2
  have hRv : ⟪R, a ∷ b ∷ 0⟫ ≤ lvB u := le_trans (le_pair_right _ _) hY
  have hv : a ∷ b ∷ 0 ≤ lvB u := le_trans (le_pair_right _ _) hRv
  exact ⟨le_trans (le_of_lt (lt_adjoin _ _)) hv,
    le_trans (le_of_lt (lt_trans (lt_adjoin _ _) (lt_adjoin' _ _))) hv⟩

theorem qVec_entries {w ℓ n c₀ : V} (hc₀ : 1 ≤ c₀) (hw : IsSemitermVec ℒₛₑₜ ℓ n w)
    (hwb : ∀ i < ℓ, w.[i] ≤ lvB c₀) (hwv : ∀ i < ℓ, IsVarTerm w.[i]) :
    (∀ i < ℓ + 1, (qVec ℒₛₑₜ w).[i] ≤ lvB (c₀ + 1)) ∧
      (∀ i < ℓ + 1, IsVarTerm (qVec ℒₛₑₜ w).[i]) := by
  have hlen : len w = ℓ := hw.isUTerm.lh.symm
  constructor
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp only [qVec, nth_adjoin_zero]
      exact le_trans (by simp [qqBvar, pair]) (le_trans (by norm_num : (1 : V) ≤ 4)
        (four_le_lvB le_add_self))
    · have hj : j < ℓ := by simpa using hi
      simp only [qVec, nth_adjoin_succ]
      rw [hlen, nth_termBShiftVec hw.isUTerm hj]
      refine le_trans (bShift_var_le (hwv j hj)) ?_
      rw [lvB_succ]
      exact mul_le_mul (four_le_lvB hc₀) (hwb j hj) (Arithmetic.zero_le _) (Arithmetic.zero_le _)
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp only [qVec, nth_adjoin_zero]
      exact isVarTerm_bvar 0
    · have hj : j < ℓ := by simpa using hi
      simp only [qVec, nth_adjoin_succ]
      rw [hlen, nth_termBShiftVec hw.isUTerm hj]
      exact bShift_isVar (hwv j hj)

theorem lvB_two : lvB (2 : V) = 16 := by
  unfold lvB
  rw [exp_two, show (4 : V) = 2 * 2 by norm_num, exp_even, exp_two]
  norm_num

theorem tag_le_lvB {k m : V} (hk : k ≤ 16) (hm : 2 ≤ m) : k ≤ lvB m :=
  le_trans hk (le_trans (le_of_eq lvB_two.symm) (lvB_mono hm))

theorem pair_lvB_le {a b u v : V} (hu : 2 ≤ u) (huv : u + 2 ≤ v) (ha : a ≤ lvB u)
    (hb : b ≤ lvB u) : ⟪a, b⟫ + 1 ≤ lvB v :=
  le_trans (pair_lvB hu ha hb) (lvB_mono huv)

theorem slack4 (m : V) : m + 2 + 2 ≤ m + 10 := by
  rw [show m + 2 + 2 = m + 4 by ring]
  exact _root_.add_le_add le_rfl (by norm_num)

theorem slack3 (m : V) : m + 1 + 2 ≤ m + 10 := by
  rw [show m + 1 + 2 = m + 3 by ring]
  exact _root_.add_le_add le_rfl (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **Substitution of variable terms multiplies levels**: entries at level
`c₀` send a level-`u` formula to level `10·(u+1) + c₀`. -/
theorem subst_level : ∀ u : V, ∀ x : V, x ≤ lvB u → IsUFormula ℒₛₑₜ x →
    ∀ c₀ ℓ n w : V, 1 ≤ c₀ → IsSemitermVec ℒₛₑₜ ℓ n w → (∀ i < ℓ, w.[i] ≤ lvB c₀) →
      (∀ i < ℓ, IsVarTerm w.[i]) → subst ℒₛₑₜ w x ≤ lvB (10 * (u + 1) + c₀) := by
  intro u
  induction u using ISigma1.pi1_succ_induction
  · simp only [lvB, IsVarTerm]
    definability
  · intro x hx hxF
    exact absurd rfl (formula_level_pos hx hxF)
  · case succ u ih =>
    intro x hx hxF c₀ ℓ n w hc₀ hw hwb hwv
    have hm := two_le_m u c₀
    rw [show 10 * (u + 1 + 1) + c₀ = 10 * (u + 1) + c₀ + 10 by ring]
    have hm10 : u + 1 ≤ 10 * (u + 1) + c₀ + 10 :=
      le_trans (le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
        le_self_add) le_self_add
    have hlen : len w = ℓ := hw.isUTerm.lh.symm
    rcases hxF.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
        ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨rfl, hR01⟩ := isRel_set hR
      obtain ⟨t₁, t₂, rfl, ht₁, ht₂⟩ := vec_two hv
      rw [substs_rel hR hv, termSubstVec_cons₂ ht₁ ht₂]
      have hx' : ⟪(0 : V), 2, R, t₁ ∷ t₂ ∷ 0⟫ + 1 ≤ lvB (u + 1) := hx
      obtain ⟨h₁, h₂⟩ := atom_children hx'
      have hR1 : R ≤ 1 := by rcases hR01 with rfl | rfl <;> simp
      exact atom_rebuild hm (by simp) hR1
        (lift_lvB (termSubst_var_le hlen hwb ht₁ h₁) (by
          calc u + c₀ ≤ 10 * (u + 1) + c₀ := _root_.add_le_add
                (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
                le_rfl
            _ = _ := rfl))
        (lift_lvB (termSubst_var_le hlen hwb ht₂ h₂) (by
          calc u + c₀ ≤ 10 * (u + 1) + c₀ := _root_.add_le_add
                (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
                le_rfl
            _ = _ := rfl))
    · obtain ⟨rfl, hR01⟩ := isRel_set hR
      obtain ⟨t₁, t₂, rfl, ht₁, ht₂⟩ := vec_two hv
      rw [substs_nrel hR hv, termSubstVec_cons₂ ht₁ ht₂]
      have hx' : ⟪(1 : V), 2, R, t₁ ∷ t₂ ∷ 0⟫ + 1 ≤ lvB (u + 1) := hx
      obtain ⟨h₁, h₂⟩ := atom_children hx'
      have hR1 : R ≤ 1 := by rcases hR01 with rfl | rfl <;> simp
      exact atom_rebuild hm le_rfl hR1
        (lift_lvB (termSubst_var_le hlen hwb ht₁ h₁) (by
          calc u + c₀ ≤ 10 * (u + 1) + c₀ := _root_.add_le_add
                (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
                le_rfl
            _ = _ := rfl))
        (lift_lvB (termSubst_var_le hlen hwb ht₂ h₂) (by
          calc u + c₀ ≤ 10 * (u + 1) + c₀ := _root_.add_le_add
                (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
                le_rfl
            _ = _ := rfl))
    · rw [substs_verum]
      exact lift_lvB hx hm10
    · rw [substs_falsum]
      exact lift_lvB hx hm10
    · rw [substs_and hp hq]
      have hx' : ⟪(4 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      have ihp := ih p (le_trans (le_pair_left _ _) hY) hp c₀ ℓ n w hc₀ hw hwb hwv
      have ihq := ih q (le_trans (le_pair_right _ _) hY) hq c₀ ℓ n w hc₀ hw hwb hwv
      exact pair_lvB_le (le_trans hm le_self_add) (slack4 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) (pair_lvB' hm ihp ihq)
    · rw [substs_or hp hq]
      have hx' : ⟪(5 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      have ihp := ih p (le_trans (le_pair_left _ _) hY) hp c₀ ℓ n w hc₀ hw hwb hwv
      have ihq := ih q (le_trans (le_pair_right _ _) hY) hq c₀ ℓ n w hc₀ hw hwb hwv
      exact pair_lvB_le (le_trans hm le_self_add) (slack4 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) (pair_lvB' hm ihp ihq)
    · rw [substs_all hp]
      have hx' : ⟪(6 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      obtain ⟨hqb, hqv⟩ := qVec_entries hc₀ hw hwb hwv
      have ihp := ih p (pair_children hx').2 hp (c₀ + 1) (ℓ + 1) (n + 1) (qVec ℒₛₑₜ w)
        (le_trans hc₀ le_self_add) hw.qVec hqb hqv
      rw [show 10 * (u + 1) + (c₀ + 1) = 10 * (u + 1) + c₀ + 1 by ring] at ihp
      exact pair_lvB_le (le_trans hm le_self_add) (slack3 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) ihp
    · rw [substs_ex hp]
      have hx' : ⟪(7 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      obtain ⟨hqb, hqv⟩ := qVec_entries hc₀ hw hwb hwv
      have ihp := ih p (pair_children hx').2 hp (c₀ + 1) (ℓ + 1) (n + 1) (qVec ℒₛₑₜ w)
        (le_trans hc₀ le_self_add) hw.qVec hqb hqv
      rw [show 10 * (u + 1) + (c₀ + 1) = 10 * (u + 1) + c₀ + 1 by ring] at ihp
      exact pair_lvB_le (le_trans hm le_self_add) (slack3 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) ihp

set_option maxHeartbeats 2000000 in
/-- **Negation multiplies levels**: a level-`u` formula has a level-`10·(u+1)`
negation. -/
theorem neg_level : ∀ u : V, ∀ x : V, x ≤ lvB u → IsUFormula ℒₛₑₜ x →
    neg ℒₛₑₜ x ≤ lvB (10 * (u + 1)) := by
  intro u
  induction u using ISigma1.pi1_succ_induction
  · simp only [lvB]
    definability
  · intro x hx hxF
    exact absurd rfl (formula_level_pos hx hxF)
  · case succ u ih =>
    intro x hx hxF
    have hm : (2 : V) ≤ 10 * (u + 1) := by simpa using two_le_m u 0
    rw [show 10 * (u + 1 + 1) = 10 * (u + 1) + 10 by ring]
    have hu1 : u + 1 ≤ 10 * (u + 1) := le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)
    rcases hxF.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
        ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [neg_rel hR hv]
      have hx' : ⟪(0 : V), ⟪k, ⟪R, v⟫⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      exact pair_lvB_le hm (le_trans (_root_.add_le_add le_rfl (by norm_num)) le_rfl)
        (tag_le_lvB (by norm_num) hm) (lift_lvB hY (le_trans (le_of_lt (lt_add_one u)) hu1))
    · rw [neg_nrel hR hv]
      have hx' : ⟪(1 : V), ⟪k, ⟪R, v⟫⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      exact pair_lvB_le hm (le_trans (_root_.add_le_add le_rfl (by norm_num)) le_rfl)
        (tag_le_lvB (by norm_num) hm) (lift_lvB hY (le_trans (le_of_lt (lt_add_one u)) hu1))
    · rw [neg_verum]
      exact le_trans (pair_lvB_le (u := 2) le_rfl (by
          calc (2 : V) + 2 ≤ 10 := by norm_num
            _ ≤ 10 * (u + 1) + 10 := le_add_self)
        (tag_le_lvB (by norm_num) le_rfl) (Arithmetic.zero_le _)) le_rfl
    · rw [neg_falsum]
      exact le_trans (pair_lvB_le (u := 2) le_rfl (by
          calc (2 : V) + 2 ≤ 10 := by norm_num
            _ ≤ 10 * (u + 1) + 10 := le_add_self)
        (tag_le_lvB (by norm_num) le_rfl) (Arithmetic.zero_le _)) le_rfl
    · rw [neg_and hp hq]
      have hx' : ⟪(4 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      have ihp := ih p (le_trans (le_pair_left _ _) hY) hp
      have ihq := ih q (le_trans (le_pair_right _ _) hY) hq
      exact pair_lvB_le (le_trans hm le_self_add) (slack4 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) (pair_lvB' hm ihp ihq)
    · rw [neg_or hp hq]
      have hx' : ⟪(5 : V), ⟪p, q⟫⟫ + 1 ≤ lvB (u + 1) := hx
      have hY := (pair_children hx').2
      have ihp := ih p (le_trans (le_pair_left _ _) hY) hp
      have ihq := ih q (le_trans (le_pair_right _ _) hY) hq
      exact pair_lvB_le (le_trans hm le_self_add) (slack4 _)
        (tag_le_lvB (by norm_num) (le_trans hm le_self_add)) (pair_lvB' hm ihp ihq)
    · rw [neg_all hp]
      have hx' : ⟪(6 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      have ihp := ih p (pair_children hx').2 hp
      exact pair_lvB_le hm (le_trans (_root_.add_le_add le_rfl (by norm_num)) le_rfl)
        (tag_le_lvB (by norm_num) hm) ihp
    · rw [neg_ex hp]
      have hx' : ⟪(7 : V), p⟫ + 1 ≤ lvB (u + 1) := hx
      have ihp := ih p (pair_children hx').2 hp
      exact pair_lvB_le hm (le_trans (_root_.add_le_add le_rfl (by norm_num)) le_rfl)
        (tag_le_lvB (by norm_num) hm) ihp

end Main

end LeanProofs.ZFCinPA.SetCodeLevels
