import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_local_shiftedPower_le_later_work
    (A C Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hA : 2 ≤ A) (hC : C ≤ A) (hn : 1 ≤ n) :
    let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
      0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
    (t + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  intro t
  have hcap : (t + C) ^ C ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    simpa only [t, preparedFiniteForwardPairedSourcePrecision_model] using
      preparedFiniteForward_phase_cap A stageCountConstant 0 C hx hg hs hC
  have hnext : preparedFiniteForwardCap A stageCountConstant 0 x ≤
      preparedFiniteForwardParameter A stageCountConstant 1 x := by
    rw [preparedFiniteForwardParameter_succ]
    have hparameter := preparedFiniteForwardParameter_nonneg A stageCountConstant 0 hx
    have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant 0 hx
    linarith only [hparameter, hbranch]
  have hlater := preparedFiniteForwardParameter_monotone A stageCountConstant hx hn
  have hwork := (preparedFiniteForward_model_scalar_bounds A stageCountConstant n 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)).2.1
  exact hcap.trans (hnext.trans (hlater.trans hwork))

theorem exists_preparedFiniteForward_local_polynomial_le_later_work
    (Cbase : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog f : ℝ},
      0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → C ≤ A → 1 ≤ n →
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
      f ∈ Set.Icc 0 ((t + Cbase) ^ Cbase) →
      P.eval₂ (Nat.castRingHom ℝ) f ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  let Q := P.comp ((Polynomial.X + Polynomial.C Cbase) ^ Cbase)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant n x gainLog stageLog f hx hg hs hCA hn t hf
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant 0 false hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx)
  have heval : P.eval₂ (Nat.castRingHom ℝ) f ≤
      P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) := by
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.1 hf.2 k) (Nat.cast_nonneg _)
  have hbound : P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) ≤ (t + C) ^ C := by
    simpa [Q, Polynomial.eval₂_comp, Polynomial.eval₂_pow] using hpoly t ht
  exact heval.trans (hbound.trans
    (preparedFiniteForward_local_shiftedPower_le_later_work A C Cdirect stageCountConstant n
      hx hg hs (hC.trans hCA) hCA hn))

end Erdos3.VectorPolynomial

end

end OAI
