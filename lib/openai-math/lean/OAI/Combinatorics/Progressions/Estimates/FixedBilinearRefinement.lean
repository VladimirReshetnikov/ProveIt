import OAI.Combinatorics.Progressions.Dynamics.FixedRefinementBudget

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem fixed_bilinear_refinement_step
    (B₀ : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 2) (hBrank : 1 ≤ B₀.rank)
    {p R H P W : ℝ} (hepsilon : 0 < epsilon) (hp : 512 ≤ p) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hBwide : Real.exp (-R) ≤ B₀.radius)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8))
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hbudget : refinementComparisonBudget B₀.rank p R epsilon ≤ P)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + ((1 / 4 : ℝ) + 1) + Real.log 3) * p ≤
      ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C : CyclicBohr.Set N, C.IsRankRegular → 0 < C.radius →
      1 ≤ C.rank → C.rank ≤ B₀.rank + unbalancedRankExtra γ p H →
      Real.exp (-(R + refinementRoundLoss B₀.rank p H epsilon)) ≤ C.radius → C.radius ≤ 2 →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      (refinementContraction epsilon * T + 4 * Real.exp (-p / 4)) := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  let scale := localizedAverageScale B₀.rank W (Real.exp (-(3 * p)))
  obtain ⟨_, hscale, hscaleError, hscaleLog⟩ := fixed_refinement_scale_spec B₀.rank hp0 hW hWcap
  have hscaleLoss : 0 ≤ refinementScaleLoss B₀.rank p := by
    unfold refinementScaleLoss
    positivity
  obtain ⟨hRD, L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hSLwidth, hSwidth,
      hSrank, hLshape, hSB, hrank, hwidth, hSwide, hSL, hmoment, hkappa, herror, hmatching⟩ :=
    exists_refinement_matching_geometry B₀ hBpos hB₀ hBwidth hBrank
      (E := 2 * p) (J := 2 * p) (M := Real.exp p) (p := p) (R := R)
      (T := refinementScaleLoss B₀.rank p) hW hWcap (by positivity) (by positivity)
      (Real.exp_nonneg p) le_rfl hp1 hH (by positivity) hscaleLoss hR
      (flatComparisonDelta_spec hepsilon).1 hBwide hscaleLog
  simp only [refinementMatchingLoss_eq, refinementRoundLoss_eq] at hRD hLshape hwidth hSwide
  have hSrankEq : S.rank = B₀.rank := congrArg Finset.card (hSfreq.trans hLfreq)
  let w := B₀.radius * Real.exp (-refinementRoundLoss B₀.rank p H epsilon)
  have hwpos : 0 < w := mul_pos hBpos (Real.exp_pos _)
  have hround := two_le_refinementRoundLoss B₀.rank hp0 hH hepsilon
  have hexp : Real.exp (-refinementRoundLoss B₀.rank p H epsilon) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
          (show (2 : ℝ) ≤ Real.exp 2 by linarith [Real.add_one_le_exp 2])
  have hw1 : w ≤ 1 := by
    have h := mul_le_mul hBwidth hexp (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [w]
    linarith
  have hwlower : Real.exp (-(R + refinementRoundLoss B₀.rank p H epsilon)) ≤ w := by
    rw [neg_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hBwide (Real.exp_nonneg _)
  have hchild : ∀ C, Peeling.admissibleBohrShape B₀ scale (unbalancedRankExtra γ p H) w C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T := by
    apply admissible_child_bound_of_bounded_shapes B₀ hwpos hw1 (by omega)
    intro C hCreg hCpos hCrank hCsize hCwidth hCwide
    exact hchildren C hCreg hCpos hCrank hCsize (hwlower.trans hCwidth) hCwide
  have hbud := max_le_iff.mp hbudget
  have hcomplexity : 2 * (S.rank : ℝ) + p + ((1 / 4 : ℝ) + 2) * p +
      (R + refinementMatchingLoss B₀.rank p epsilon) + 1612 ≤ P := by
    simpa only [hSrankEq] using hbud.1
  have hprecision : ((1 / 4 : ℝ) + 2) * p + 2 + (S.rank : ℝ) *
      (R + refinementMatchingLoss B₀.rank p epsilon + 10) ≤ P := by
    simpa only [hSrankEq] using hbud.2
  have h := normalized_bilinear_refinement_step B₀ L S hB₀ hLreg hSpos hSwidth hSreg hSrank
    hSfreq hSLwidth hepsilon hp1 (by norm_num : (0 : ℝ) ≤ 1 / 4) hRD hH
    hSL hkappa hscale hSB hrank hwidth hLshape A B hA hB
    (by norm_num : (0 : ℝ) < 1 / 256) (by norm_num : (0 : ℝ) < 16)
    (Real.exp_pos (-p / 2)) fixed_refinement_thresholds.1 fixed_refinement_thresholds.2
    (Real.exp_pos p) le_rfl (refinement_cap_cutoff hp) (refinement_tiny_cutoff hWcap)
    hmoment herror hSwide hcomplexity hprecision hcompare hW hWcap (by positivity) (by positivity) ha
    (fun origin f g hf hg => hmatching (fun r => A (origin + r) - (1 + epsilon) * B (origin + r))
      f g (fun r => ha (origin + r)) hf hg) m hm horder horders hT hchild
  apply h.mono
  have herr := refinement_total_error hp0 hscaleError
  rw [← refinementContraction_eq]
  nlinarith only [herr]

end Erdos3.CellRefinement

end

end OAI
