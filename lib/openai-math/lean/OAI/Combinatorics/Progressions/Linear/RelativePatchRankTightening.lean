import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3

theorem RelativePatchSliceConclusion.tighten_rank
    {X : Type*} [Fintype X] {s : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost) :
    RelativePatchSliceConclusion s N f target (min rankBound ⌊cost⌋₊) cost := by
  obtain ⟨q,hq,S,d,A,hlength,hd,hcomplexity,hscore⟩ := h
  have hdp : d ≤ ⌊cost⌋₊ := Nat.le_floor ((relativePatchComplexity_rank_le A).trans hcomplexity)
  exact ⟨q,hq,S,d,A,hlength,le_min hd hdp,hcomplexity,hscore⟩

theorem RelativePatchAbsoluteRule.tighten_rank {s n₀ d₀ : ℕ} {p a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    RelativePatchAbsoluteRule s n₀ p a Λ (min d₀ ⌊p⌋₊) := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio hsize f hf hfree hmean).tighten_rank

end Erdos3

end

end OAI
