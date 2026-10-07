import OAI.Combinatorics.Progressions.Estimates.FixedBilinearRefinement

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem refinementComparisonBudget_mono {r d : ℕ} {p R R' epsilon : ℝ}
    (hrd : r ≤ d) (hp : 0 ≤ p) (hR : 0 ≤ R) (hRR' : R ≤ R')
    (hepsilon : 0 < epsilon) :
    refinementComparisonBudget r p R epsilon ≤ refinementComparisonBudget d p R' epsilon := by
  have hr : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hm := refinementMatchingLoss_mono_rank hrd p epsilon
  have hm0 := refinementMatchingLoss_nonneg r hp hepsilon
  have hi : R + refinementMatchingLoss r p epsilon + 10 ≤
      R' + refinementMatchingLoss d p epsilon + 10 := by linarith
  have hprod := mul_le_mul hr hi (by positivity : 0 ≤ R + refinementMatchingLoss r p epsilon + 10)
    (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  unfold refinementComparisonBudget
  apply max_le_max <;> linarith

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem bohr_refinement_iteration
    (B₀ : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 2) (hBrank : 1 ≤ B₀.rank)
    {p R H P W : ℝ} (hepsilon : 0 < epsilon) (hp : 512 ≤ p) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hBwide : Real.exp (-R) ≤ B₀.radius) (n : ℕ)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8))
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + ((1 / 4 : ℝ) + 1) + Real.log 3) * p ≤
      ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    (hbudget : let d := B₀.rank + n * unbalancedRankExtra γ p H
      let loss := refinementRoundLoss d p H epsilon
      refinementComparisonBudget d p (R + n * loss) epsilon ≤ P) :
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      ((refinementContraction epsilon) ^ n * W +
        (4 * Real.exp (-p / 4)) / (1 - refinementContraction epsilon)) := by
  let extra := unbalancedRankExtra γ p H
  let d := B₀.rank + n * extra
  let loss := refinementRoundLoss d p H epsilon
  let family : ℕ → CyclicBohr.Set N → Prop := fun j C =>
    C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 2 ∧ 1 ≤ C.rank ∧
      C.rank ≤ B₀.rank + j * extra ∧ Real.exp (-(R + (j : ℝ) * loss)) ≤ C.radius
  have hp0 : 0 ≤ p := by linarith
  have hloss : 0 ≤ loss := (by linarith : (0 : ℝ) ≤ 2).trans
    (two_le_refinementRoundLoss d hp0 hH hepsilon)
  have hroot : family 0 B₀ := by
    refine ⟨hB₀, hBpos, hBwidth, hBrank, ?_, ?_⟩
    · simp
    · simpa only [Nat.cast_zero, zero_mul, add_zero] using hBwide
  apply finite_cell_refinement CyclicBohr.Set.carrier family
    (fun r => A r - (1 + epsilon) * B r) n hW
    (refinementContraction_bounds epsilon).1 (refinementContraction_bounds epsilon).2
    (by positivity) (fun r => (le_abs_self _).trans (ha r))
    (fun _ C _ => C.carrier_nonempty) ?_ B₀ hroot
  intro j hj T hT hchildren C hC
  obtain ⟨hCreg, hCpos, hCwidth, hCrank, hCsize, hCwide⟩ := hC
  have hjn : j ≤ n := Nat.le_of_lt hj
  have hjnR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hCtotal : C.rank ≤ d := hCsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_right extra hjn) _)
  have hCround : refinementRoundLoss C.rank p H epsilon ≤ loss :=
    refinementRoundLoss_mono_rank hCtotal p H epsilon
  have hRj : 0 ≤ R + (j : ℝ) * loss := by positivity
  have hRjn : R + (j : ℝ) * loss ≤ R + (n : ℝ) * loss := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hjnR hloss)
  have hCbudget : refinementComparisonBudget C.rank p (R + (j : ℝ) * loss) epsilon ≤ P :=
    (refinementComparisonBudget_mono hCtotal hp0 hRj hRjn hepsilon).trans hbudget
  apply fixed_bilinear_refinement_step C hCreg hCpos hCwidth hCrank hepsilon hp hRj hH hCwide
    A B hA hB hW hWcap ha hcompare hCbudget m hm horder horders hT
  intro D hDreg hDpos hDrank hDsize hDwide hDwidth
  apply hchildren D
  refine ⟨hDreg, hDpos, hDwidth, hDrank, ?_, ?_⟩
  · change D.rank ≤ C.rank + extra at hDsize
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hnext : R + (j : ℝ) * loss + refinementRoundLoss C.rank p H epsilon ≤
        R + ((j + 1 : ℕ) : ℝ) * loss := by
      push_cast
      nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg hnext)).trans hDwide

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem refinement_error_small {p gap : ℝ} (hgap : 0 < gap) (hp : 32 / gap ≤ p) :
    4 * Real.exp (-p / 4) ≤ gap * Real.exp (-p / 8) := by
  have hp' : 32 ≤ p * gap := (div_le_iff₀ hgap).mp hp
  have hscaled := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (p / 8)) hgap.le
  have hfour : 4 ≤ gap * Real.exp (p / 8) := by nlinarith
  calc
    _ ≤ (gap * Real.exp (p / 8)) * Real.exp (-p / 4) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem exists_quantitative_bohr_bound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (N : ℕ) [NeZero N] (B₀ : CyclicBohr.Set N) (p R P W : ℝ),
      B₀.IsRankRegular → 0 < B₀.radius → B₀.radius ≤ 2 → 1 ≤ B₀.rank →
      512 ≤ p → 32 / (1 - refinementContraction epsilon) ≤ p → 0 ≤ R →
      Real.exp (-R) ≤ B₀.radius →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      0 ≤ W → W ≤ Real.exp (p / 8) → (∀ r, |A r - (1 + epsilon) * B r| ≤ W) →
      CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B →
      (let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
       let d := B₀.rank + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
       let loss := refinementRoundLoss d p H epsilon
       refinementComparisonBudget d p (R + n * loss) epsilon ≤ P) →
      CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
        (2 * Real.exp (-p / 8)) := by
  obtain ⟨C, H, _, hH, hmoment⟩ :=
    exists_refinement_moment_orders (epsilon := epsilon) (D := 1 / 4) (by norm_num)
  refine ⟨H, hH, ?_⟩
  intro N hN B₀ p R P W hB₀ hBpos hBwidth hBrank hp hplarge hR hBwide
    A B hA hB hW hWcap ha hcompare hbudget
  obtain ⟨m, hm, _, horder, horders⟩ := hmoment p (by linarith)
  let rho := refinementContraction epsilon
  let n := ⌈(p / 4) / (1 - rho)⌉₊
  have hrho : 0 ≤ rho := (refinementContraction_bounds epsilon).1
  have hrho1 : rho < 1 := (refinementContraction_bounds epsilon).2
  have hgap : 0 < 1 - rho := by linarith
  have hdepth : p / 8 + p / 8 ≤ (1 - rho) * (n : ℝ) := by
    have h := (div_le_iff₀ hgap).mp (Nat.le_ceil ((p / 4) / (1 - rho)))
    dsimp only [n]
    nlinarith
  have hnoise : 4 * Real.exp (-p / 4) ≤ (1 - rho) * Real.exp (-(p / 8)) := by
    simpa only [neg_div] using refinement_error_small hgap hplarge
  have h := bohr_refinement_iteration B₀ hB₀ hBpos hBwidth hBrank
    hepsilon hp hR hH hBwide n A B hA hB hW hWcap ha hcompare m hm horder horders hbudget
  apply h.mono
  simpa only [neg_div] using refinement_coefficient_le hrho hrho1 hW hWcap hdepth hnoise

end Erdos3.CellRefinement

end

end OAI
