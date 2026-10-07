import OAI.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

theorem exists_selected_correlator_quadruples_budget {s r N : ℕ} [NeZero N]
    {p : ℝ} {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-((p + 3) ^ 3)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ W.shifts ∧ t.2.1 - t.1 ∈ W.shifts ∧
        t.2.2 ∈ W.shifts ∧ t.2.2 - t.1 ∈ W.shifts ∧
        Real.exp (-((p + 3) ^ 3)) ≤ additiveQuadrupleCorrelation W.selectedCorrelator t.1 t.2.1 t.2.2 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  have hcost : 12 * p + 1 ≤ (p + 3) ^ 3 := by
    nlinarith only [hp, pow_nonneg hp 3, sq_nonneg p]
  have hcost' : 8 * p + 1 ≤ (p + 3) ^ 3 := by linarith only [hcost, hp]
  have hdensity : Real.exp (-((p + 3) ^ 3)) ≤ Real.exp (-(12 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hcost])).trans (exp_sub_one_le_half_exp (-(12 * p)))
  have hcorrelation : Real.exp (-((p + 3) ^ 3)) ≤ Real.exp (-(8 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hcost'])).trans (exp_sub_one_le_half_exp (-(8 * p)))
  obtain ⟨Q, hQ, hdense, hcorr⟩ := W.exists_selected_correlator_quadruples hf
  refine ⟨Q, hQ, (mul_le_mul_of_nonneg_right hdensity (by positivity)).trans hdense, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  exact ⟨h₁, h₂, h₃, h₄, hcorrelation.trans hc⟩

end Erdos3.NativeCorrelationStructure

end

end OAI
