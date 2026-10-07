import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem anova_bootstrap_le {U D E : ℝ} (_hU : 0 ≤ U) (hD : 0 ≤ D) (hE : E ≤ D)
    (h : U ^ 2 ≤ D * max U E) : U ≤ D := by
  by_cases hUE : U ≤ E
  · rw [max_eq_right hUE] at h
    have hm := mul_le_mul_of_nonneg_left hE hD
    nlinarith
  · rw [max_eq_left (le_of_not_ge hUE)] at h
    nlinarith

end Erdos3

end

end OAI
