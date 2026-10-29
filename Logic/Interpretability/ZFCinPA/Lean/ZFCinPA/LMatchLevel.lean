import ZFCinPA.LMatch
import ZFCinPA.SetCodeLevels

/-!
# The matching codes `mVal j` have an elementary size bound

`LMatch.mVal j` is defined by an internal primitive recursion of length `j`,
each step substituting into the shift of the previous code. In every model of
`𝗜𝚺₁`, with the fixed constant `Cm = ⌜funcS⌝ + zT + eT + 40`:

`mVal j ≤ lvB (Cm · 16^j) = 2^(2^(Cm·16^j))` (`mVal_le`).

Each step multiplies the level by `10` and adds a constant (`SetCodeLevels`),
so the bound is a fixed-height tower in `j`. This is the first internal
iteration of the constructible-universe obligations given an explicit
elementary bound. A per-step value bound (double exponential in the previous
code) would give a tower of height `≈ 2j` instead.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.LMatchLevel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.LMatch LeanProofs.ZFCinPA.SetCodeLevels
open LeanProofs.BoundedPAConsistency.SubstBound LeanProofs.BoundedPAConsistency.SizedDerivation

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fixed constant of the matching-code bound. -/
def Cm : V := (fT (V := V)).val + (zT (V := V)).val + (eT (V := V)).val + 40

theorem forty_le_Cm : (40 : V) ≤ Cm := le_add_self

theorem zT_le_Cm : (zT (V := V)).val ≤ Cm := by
  unfold Cm
  exact le_trans (le_trans le_add_self le_self_add) le_self_add

theorem eT_le_Cm : (eT (V := V)).val ≤ Cm := by
  unfold Cm
  exact le_trans le_add_self le_self_add

theorem fT_le_Cm : (fT (V := V)).val ≤ Cm := by
  unfold Cm
  exact le_trans (le_trans le_self_add le_self_add) le_self_add

/-- One matching step: level `u ≥ Cm` goes to level `16·u`. -/
theorem mVal_step {j u : V} (hu : Cm ≤ u) (h : mVal j ≤ lvB u) :
    mVal (j + 1) ≤ lvB (16 * u) := by
  rw [mVal_succ]
  have hF : IsUFormula ℒₛₑₜ (shift ℒₛₑₜ (mVal j)) :=
    (isSemiformula_mVal j).shift.isUFormula
  have hsh := shift_level h
  have hw : IsSemitermVec ℒₛₑₜ 1 2 (^#1 ∷ 0 : V) := by
    simp
  have hS := subst_level (u + 1) _ hsh hF 1 1 2 (^#1 ∷ 0) le_rfl hw
    (fun i hi => by
      have : i = 0 := by simpa using hi
      subst this
      simp only [nth_adjoin_zero]
      exact le_trans (by simp [qqBvar, pair]; norm_num) (le_of_eq lvB_one.symm))
    (fun i hi => by
      have : i = 0 := by simpa using hi
      subst this
      simpa using isVarTerm_bvar (1 : V))
  set m := 10 * (u + 1 + 1) + 1 with hm_def
  have hm2 : (2 : V) ≤ m := le_trans (by norm_num : (2 : V) ≤ 10)
    (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self) le_self_add)
  have hum : u ≤ m := le_trans (le_trans le_self_add le_self_add)
    (le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)) le_self_add)
  have hz : (zT (V := V)).val ≤ lvB m := lift_lvB (le_lvB_self _) (le_trans zT_le_Cm (le_trans hu hum))
  have he : (eT (V := V)).val ≤ lvB m := lift_lvB (le_lvB_self _) (le_trans eT_le_Cm (le_trans hu hum))
  -- eT ⋏ S
  have a1 := pair_lvB' hm2 he hS
  have a2 := pair_lvB (le_trans hm2 le_self_add) (tag_le_lvB (k := 4) (by norm_num) (le_trans hm2 le_self_add)) a1
  -- zT ⋏ (eT ⋏ S)
  have a3 := pair_lvB' (le_trans hm2 (le_trans le_self_add le_self_add))
    (lift_lvB hz (le_trans le_self_add le_self_add)) a2
  have a4 := pair_lvB (le_trans hm2 (le_trans le_self_add (le_trans le_self_add le_self_add)))
    (tag_le_lvB (k := 4) (by norm_num) (le_trans hm2 (le_trans le_self_add (le_trans le_self_add le_self_add)))) a3
  -- two existentials
  have a5 := pair_lvB (le_trans hm2 (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add le_self_add))))
    (tag_le_lvB (k := 7) (by norm_num) (le_trans hm2 (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add le_self_add))))) a4
  have a6 := pair_lvB (le_trans hm2 (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add (le_trans le_self_add le_self_add)))))
    (tag_le_lvB (k := 7) (by norm_num) (le_trans hm2 (le_trans le_self_add (le_trans le_self_add
      (le_trans le_self_add (le_trans le_self_add le_self_add)))))) a5
  refine le_trans a6 (lvB_mono ?_)
  have h33 : (33 : V) ≤ 6 * u := le_trans (by norm_num : (33 : V) ≤ 6 * 40)
    (mul_le_mul_of_nonneg_left (le_trans forty_le_Cm hu) (Arithmetic.zero_le _))
  calc m + 2 + 2 + 2 + 2 + 2 + 2 = 10 * u + 33 := by rw [hm_def]; ring
    _ ≤ 10 * u + 6 * u := _root_.add_le_add le_rfl h33
    _ = 16 * u := by ring

/-- **The matching codes grow at most as `2^(2^(Cm·16^j))`.** -/
theorem mVal_le (j : V) : mVal j ≤ lvB (Cm * Exp.exp (4 * j)) := by
  induction j using ISigma1.sigma1_succ_induction
  · simp only [lvB]
    definability
  · simp only [mVal_zero, mul_zero, exp_zero, mul_one]
    exact lift_lvB (le_lvB_self _) fT_le_Cm
  · case succ j ih =>
    have hu : Cm ≤ Cm * Exp.exp (4 * j) := le_mul_of_one_le_right (Arithmetic.zero_le _) (one_le_exp _)
    refine le_trans (mVal_step hu ih) (lvB_mono (le_of_eq ?_))
    rw [show 4 * (j + 1) = 4 * j + 4 by ring, exp_add,
      show Exp.exp (4 : V) = 16 by rw [show (4 : V) = 2 * 2 by norm_num, exp_even, exp_two]; norm_num]
    ring

end LeanProofs.ZFCinPA.LMatchLevel
