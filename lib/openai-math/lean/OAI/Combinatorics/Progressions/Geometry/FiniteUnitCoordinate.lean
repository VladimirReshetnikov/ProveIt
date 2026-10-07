import OAI.Combinatorics.Progressions.Linear.FiniteNormalizedFrame

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_unit_coordinate {I : Type*} [Fintype I] (v : I → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∃ i, 1 / (Fintype.card I + 1 : ℝ) ≤ ‖v i‖ := by
  classical
  have hpos : (0 : ℝ) < Fintype.card I + 1 := by positivity
  by_contra h
  push Not at h
  have hn : ‖v‖ < 1 / (Fintype.card I + 1 : ℝ) :=
    (pi_norm_lt_iff (by positivity)).mpr h
  let V : EuclideanSpace ℂ I := WithLp.toLp 2 v
  have hV : ‖V‖ = 1 := by
    have hs : ‖V‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact hv
    nlinarith [norm_nonneg V]
  have hbound := euclidean_norm_le_card_add_one_mul V (norm_nonneg v)
    (fun i => norm_le_pi_norm v i)
  rw [hV] at hbound
  have hsmall := (lt_div_iff₀ hpos).mp hn
  nlinarith

end Erdos3

end

end OAI
