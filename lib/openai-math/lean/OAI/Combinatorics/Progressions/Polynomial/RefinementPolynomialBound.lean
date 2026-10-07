import OAI.Combinatorics.Progressions.Fourier.QuantitativeBohrBound

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution Polynomial

noncomputable def refinementRankPolynomial (C : ℕ) : Polynomial ℕ :=
  Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 + 1

noncomputable def refinementDepthPolynomial (C : ℕ) : Polynomial ℕ := Polynomial.C C * X + 1

noncomputable def refinementFinalRankPolynomial (C : ℕ) : Polynomial ℕ :=
  1 + refinementDepthPolynomial C * refinementRankPolynomial C

noncomputable def refinementMatchPolynomial (C : ℕ) : Polynomial ℕ :=
  5 * refinementFinalRankPolynomial C + 13 * X + 2 * Polynomial.C C + 8020

noncomputable def refinementUnbalancedPolynomial (C : ℕ) : Polynomial ℕ :=
  2 * refinementFinalRankPolynomial C +
    Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 +
    2 * Polynomial.C C * X ^ 2 + 2 * X + 2 * Polynomial.C C + 3209 +
    Polynomial.C C * (3 + (3 * Polynomial.C C + 1) * X ^ 2 + refinementFinalRankPolynomial C)

noncomputable def refinementRoundPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementMatchPolynomial C + refinementFinalRankPolynomial C + 3 * X + 1602 +
    refinementUnbalancedPolynomial C

noncomputable def refinementWidthPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementDepthPolynomial C * refinementRoundPolynomial C

noncomputable def refinementCostPolynomial (C : ℕ) : Polynomial ℕ :=
  (2 * refinementFinalRankPolynomial C + 4 * X + refinementWidthPolynomial C +
    refinementMatchPolynomial C + 1612) +
  (3 * X + 2 + refinementFinalRankPolynomial C *
    (refinementWidthPolynomial C + refinementMatchPolynomial C + 10))

theorem refinementRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
  simp [refinementRankPolynomial, Polynomial.eval₂_pow]

theorem refinementDepthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p = (C : ℝ) * p + 1 := by
  simp [refinementDepthPolynomial]

theorem refinementFinalRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      1 + (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementFinalRankPolynomial]

theorem refinementMatchPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      5 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        13 * p + 2 * (C : ℝ) + 8020 := by
  simp [refinementMatchPolynomial]

theorem refinementUnbalancedPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 +
          (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p) := by
  simp [refinementUnbalancedPolynomial, Polynomial.eval₂_pow]

theorem refinementRoundPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 3 * p + 1602 +
          (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementRoundPolynomial]

theorem refinementWidthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementWidthPolynomial]

theorem refinementCostPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 4 * p +
        (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 1612) +
      (3 * p + 2 + (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        ((refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 10)) := by
  simp [refinementCostPolynomial]

theorem refinement_cost_le_polynomial {epsilon H p : ℝ} (hepsilon : 0 < epsilon)
    (hH : 0 ≤ H) (hp : 0 ≤ p) (C : ℕ)
    (hHC : H ≤ C)
    (hKC : CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) ≤ C)
    (hDC : localMomentErrorBudget (flatComparisonDelta epsilon) ≤ C)
    (hEC : unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) ≤ C)
    (hgapC : 1 / (1 - refinementContraction epsilon) ≤ C) :
    let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
    let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
    refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
      (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  intro n d
  let ev := fun Q : Polynomial ℕ => Q.eval₂ (Nat.castRingHom ℝ) p
  have hev (Q : Polynomial ℕ) : 0 ≤ ev Q := natPolynomial_eval_nonneg Q hp
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hK : 0 ≤ CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) :=
    (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have haeq : ev (refinementRankPolynomial C) =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
    exact refinementRankPolynomial_eval C p
  have hneq : ev (refinementDepthPolynomial C) = (C : ℝ) * p + 1 := by
    exact refinementDepthPolynomial_eval C p
  have hdeq : ev (refinementFinalRankPolynomial C) =
      1 + ev (refinementDepthPolynomial C) * ev (refinementRankPolynomial C) := by
    exact refinementFinalRankPolynomial_eval C p
  have hmeq : ev (refinementMatchPolynomial C) =
      5 * ev (refinementFinalRankPolynomial C) + 13 * p + 2 * (C : ℝ) + 8020 := by
    exact refinementMatchPolynomial_eval C p
  have hueq : ev (refinementUnbalancedPolynomial C) =
      2 * ev (refinementFinalRankPolynomial C) +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 + ev (refinementFinalRankPolynomial C)) := by
    exact refinementUnbalancedPolynomial_eval C p
  have hleq : ev (refinementRoundPolynomial C) =
      ev (refinementMatchPolynomial C) + ev (refinementFinalRankPolynomial C) +
        3 * p + 1602 + ev (refinementUnbalancedPolynomial C) := by
    exact refinementRoundPolynomial_eval C p
  have hreq : ev (refinementWidthPolynomial C) =
      ev (refinementDepthPolynomial C) * ev (refinementRoundPolynomial C) := by
    exact refinementWidthPolynomial_eval C p
  have hqeq : ev (refinementCostPolynomial C) =
      (2 * ev (refinementFinalRankPolynomial C) + 4 * p + ev (refinementWidthPolynomial C) +
        ev (refinementMatchPolynomial C) + 1612) +
      (3 * p + 2 + ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10)) := by
    exact refinementCostPolynomial_eval C p
  have ha : (unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℝ) ≤
      ev (refinementRankPolynomial C) := by
    apply (unbalancedRankExtra_le (p := p) (H := H) hc).trans
    rw [haeq]
    gcongr
  have hn : (n : ℝ) ≤ ev (refinementDepthPolynomial C) := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (p / 4) / (1 - refinementContraction epsilon)
      by positivity)).le
    have hmul := mul_le_mul_of_nonneg_right hgapC hp
    have hscale : (p / 4) / (1 - refinementContraction epsilon) ≤ (C : ℝ) * p := by
      rw [show (p / 4) / (1 - refinementContraction epsilon) =
        (1 / (1 - refinementContraction epsilon) * p) / 4 by ring]
      have hprod : 0 ≤ 1 / (1 - refinementContraction epsilon) * p := by positivity
      linarith
    rw [hneq]
    exact hceil.trans (add_le_add hscale le_rfl)
  have hd : (d : ℝ) ≤ ev (refinementFinalRankPolynomial C) := by
    rw [hdeq]
    change ((1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℕ) : ℝ) ≤ _
    push_cast
    exact add_le_add le_rfl (mul_le_mul hn ha (Nat.cast_nonneg _) (hev _))
  have hm : refinementMatchingLoss d p epsilon ≤ ev (refinementMatchPolynomial C) := by
    rw [hmeq]
    unfold refinementMatchingLoss
    linarith only [hd, hDC, hEC, hp]
  have hu : unbalancedWidthLoss d (localMomentGain (flatComparisonDelta epsilon)) p H ≤
      ev (refinementUnbalancedPolynomial C) := by
    apply (unbalancedWidthLoss_le_polynomial d (p := p) (H := H) hc).trans
    rw [hueq]
    gcongr
  have hl : refinementRoundLoss d p H epsilon ≤ ev (refinementRoundPolynomial C) := by
    rw [hleq]
    unfold refinementRoundLoss unbalancedReturnWidthLoss
    linarith only [hm, hd, hu, hp]
  have hl0 : 0 ≤ refinementRoundLoss d p H epsilon :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_refinementRoundLoss d hp hH hepsilon)
  have hr : (n : ℝ) * refinementRoundLoss d p H epsilon ≤ ev (refinementWidthPolynomial C) := by
    rw [hreq]
    exact mul_le_mul hn hl hl0 (hev _)
  have hm0 := refinementMatchingLoss_nonneg d hp hepsilon
  have hD0 := hev (refinementFinalRankPolynomial C)
  have hR0 := hev (refinementWidthPolynomial C)
  have hM0 := hev (refinementMatchPolynomial C)
  have hprod : (d : ℝ) * ((n : ℝ) * refinementRoundLoss d p H epsilon +
      refinementMatchingLoss d p epsilon + 10) ≤ ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by
    gcongr
  change refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
    ev (refinementCostPolynomial C)
  rw [hqeq]
  unfold refinementComparisonBudget
  have hprod0 : 0 ≤ ev (refinementFinalRankPolynomial C) *
      (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by positivity
  apply max_le <;> nlinarith only [hd, hm, hr, hprod, hp, hD0, hR0, hM0, hprod0]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem exists_refinement_cost_polynomial {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) :
    ∃ Q : Polynomial ℕ, ∀ p : ℝ, 0 ≤ p →
      let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
      refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
        Q.eval₂ (Nat.castRingHom ℝ) p := by
  let c := localMomentGain (flatComparisonDelta epsilon)
  let K := CyclicCrootSisask.almostPeriodicityWidthConstant (c / 64)
  let D := localMomentErrorBudget (flatComparisonDelta epsilon)
  let E := unbalancedErrorBudget c
  let r := 1 / (1 - refinementContraction epsilon)
  have hc : 0 < c := localMomentGain_pos _
  have hc1 : c ≤ 1 := (localMomentGain_le_half _).trans (by norm_num)
  have hK : 0 ≤ K := (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have hD : 0 ≤ D := (localMomentErrorBudget_spec (flatComparisonDelta_spec hepsilon).1).1
  have hE : 0 ≤ E := (unbalancedErrorBudget_spec hc hc1).1
  have hr : 0 ≤ r := by
    have hgap : 0 < 1 - refinementContraction epsilon := by
      linarith [(refinementContraction_bounds epsilon).2]
    exact (one_div_pos.mpr hgap).le
  obtain ⟨C, hC⟩ := exists_nat_ge (H + K + D + E + r)
  refine ⟨refinementCostPolynomial C, ?_⟩
  intro p hp
  exact refinement_cost_le_polynomial hepsilon hH hp C
    (by linarith) (by change K ≤ C; linarith) (by change D ≤ C; linarith)
    (by change E ≤ C; linarith) (by change r ≤ C; linarith)

theorem exists_rescaled_refinement_budget {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (A : ℝ) * (p + 1)
      let n := ⌈(q / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) q H
      refinementComparisonBudget d q (n * refinementRoundLoss d q H epsilon) epsilon ≤
        (p + 2) ^ C := by
  obtain ⟨Q, hQ⟩ := exists_refinement_cost_polynomial hepsilon hH
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_affine_budget Q A
  refine ⟨C, hC, ?_⟩
  intro p hp
  exact (hQ ((A : ℝ) * (p + 1)) (by positivity)).trans (hbound p hp)

end Erdos3.CellRefinement

end

end OAI
