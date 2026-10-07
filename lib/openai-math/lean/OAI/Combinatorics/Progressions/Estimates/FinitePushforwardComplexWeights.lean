import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

noncomputable def finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) :
    FiniteProbabilityWeights T := by
  classical
  refine ⟨fun t => ∑ u, if f u = t then p.weight u else 0, ?_, ?_⟩
  · intro t
    exact Finset.sum_nonneg (fun u _ => by split <;> simp_all only [p.nonneg, le_refl])
  · rw [Finset.sum_comm]
    simpa using p.total

theorem mean_finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℝ) :
    (p.finitePushforward f).mean g = p.mean (fun u => g (f u)) := by
  classical
  simp only [mean, finitePushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

theorem uniform_finitePushforward_mean [Nonempty U] (f : U → T) (g : T → ℝ) :
    ((uniform U).finitePushforward f).mean g = 𝔼 u, g (f u) := by
  rw [mean_finitePushforward, uniform_mean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

theorem complexMean_finitePushforward (p : FiniteProbabilityWeights U)
    (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  classical
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

theorem finitePushforward_pos_iff (p : FiniteProbabilityWeights U)
    (f : U → T) (t : T) :
    0 < (p.finitePushforward f).weight t ↔ ∃ u, f u = t ∧ 0 < p.weight u := by
  classical
  change 0 < (∑ u, if f u = t then p.weight u else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg (fun u _ =>
    ite_nonneg (p.nonneg u) (le_refl 0))]
  constructor
  · rintro ⟨u, _, hu⟩
    by_cases he : f u = t
    · exact ⟨u, he, by simpa only [he, ite_true] using hu⟩
    · simp only [he, ite_false, lt_self_iff_false] at hu
  · rintro ⟨u, he, hu⟩
    exact ⟨u, Finset.mem_univ _, by simpa only [he, ite_true] using hu⟩

end Erdos3.FiniteProbabilityWeights

end

end OAI
