import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardStage_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x gainLog stageLog : ℝ, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCumulative A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, hB, hschedule⟩ :=
    exists_preparedFiniteForwardSchedule_budget depth A stageCountConstant
  let Q : Polynomial ℕ := 8 * (Polynomial.X + Polynomial.C B) ^ B + 32
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hstage n hn
  have hbound : 8 * (x + B) ^ B + 32 ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget x hx
  have hT : 0 ≤ (x + B) ^ B := pow_nonneg (add_nonneg hx (Nat.cast_nonneg B)) _
  have hraise : (x + B) ^ B ≤ (x + C) ^ C := by linarith only [hbound, hT]
  obtain ⟨hp, hw, hcap, hcount, hbranch⟩ := hschedule x hx n hn
  have hprefix := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hprecision :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hsource :
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤
        (x + C) ^ C := by
    linarith only [hprecision.2.2.2.2, hp.2, hw.1, hw.2, hbound]
  have hmodel :
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ≤
        preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
    linarith only [hprecision.2.2.1, hw.1]
  exact ⟨⟨hp.1, hp.2.trans hraise⟩, ⟨hw.1, hw.2.trans hraise⟩,
    ⟨hcap.1, hcap.2.trans hraise⟩, ⟨hcount.1, hcount.2.trans hraise⟩,
    ⟨hbranch.1, hbranch.2.trans hraise⟩,
    ⟨hprefix.1.1, hprefix.1.2.trans (hp.2.trans hraise)⟩,
    ⟨hprefix.2.1, hprefix.2.2.trans (hp.2.trans hraise)⟩,
    ⟨hprecision.1, hmodel.trans hsource⟩, ⟨hprecision.2.1, hsource⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
