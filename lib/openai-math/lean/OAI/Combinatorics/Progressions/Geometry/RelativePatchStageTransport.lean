import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchSliceScore_antitone {X : Type*} [Fintype X] {s d q : ℕ}
    {N : X → ℕ} (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ)
    (A : PolynomialPatch X s d) {target target' : ℝ} (h : target' ≤ target) :
    relativePatchSliceScore S f target A ≤ relativePatchSliceScore S f target' A := by
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left h _)
    (A.value_mem_Icc (fun i => ((x i).val : ℝ))).1

theorem RelativePatchSliceConclusion.target_mono {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target target' cost : ℝ} {D : ℕ}
    (h : RelativePatchSliceConclusion s N f target D cost) (htarget : target' ≤ target) :
    RelativePatchSliceConclusion s N f target' D cost := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  exact ⟨q, hq, S, d, A, hlength, hd, hcomplexity,
    hscore.trans (relativePatchSliceScore_antitone S f A htarget)⟩

theorem RelativePatchSliceConclusion.later_stage_target {X : Type*} [Fintype X]
    {s stage stage' D : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {τ Λ cost : ℝ}
    (h : RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ) D cost)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hΛ : 0 ≤ Λ) (hstage : stage ≤ stage') :
    RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage' + 1) * Λ) D cost := by
  apply h.target_mono
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sub_nonneg.mpr hτ.2) (by linarith [hτ.1])
      (Nat.add_le_add_right hstage 1)) hΛ

theorem RelativePatchSliceConclusion.prescribed_discount {X : Type*} [Fintype X]
    {s stage D : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {τ ε Λ cost : ℝ}
    (h : RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ) D cost)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hΛ : 0 ≤ Λ) (hstage : stage ≤ s)
    (hbudget : ((s + 1 : ℕ) : ℝ) * τ ≤ ε) :
    RelativePatchSliceConclusion s N f ((1 - ε) * Λ) D cost :=
  h.target_mono (recursive_density_discount_scaled hΛ hτ
    (Nat.add_le_add_right hstage 1) hbudget)

theorem RelativePatchInductionRule.apply_later_discount
    {s n₀ stage stage' : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (h : RelativePatchInductionRule s n₀ stage τ cutoff cost)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hstages : stage ≤ stage')
    (p a Λ : ℝ) (d₀ : ℕ) (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ a)
    (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    (hX : (Fintype.card X : ℝ) ≤ p) (N : X → ℕ)
    (hN : ∀ i, Real.exp (cutoff p) ≤ (N i : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (d : ℕ) (A : PolynomialPatch X s d) (hA : relativePatchComplexity A ≤ p)
    (hstage : relativePatchDistinctWeights A ≤ stage)
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a A) :
    RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage' + 1) * Λ)
      (d₀ + s * d) (cost p) :=
  (h p a Λ d₀ hp ha haΛ hΛ habsolute X hX N hN f hf hfree d A hA hstage hscore).later_stage_target
    hτ (((Real.exp_pos (-p)).le.trans ha).trans haΛ) hstages

theorem RelativePatchInductionRule.apply_all_weights_discount
    {s n₀ : ℕ} {τ ε : ℝ} {cutoff cost : ℝ → ℝ}
    (h : RelativePatchInductionRule s n₀ s τ cutoff cost)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hbudget : ((s + 1 : ℕ) : ℝ) * τ ≤ ε)
    (p a Λ : ℝ) (d₀ : ℕ) (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ a)
    (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    (hX : (Fintype.card X : ℝ) ≤ p) (N : X → ℕ)
    (hN : ∀ i, Real.exp (cutoff p) ≤ (N i : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (d : ℕ) (A : PolynomialPatch X s d) (hA : relativePatchComplexity A ≤ p)
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a A) :
    RelativePatchSliceConclusion s N f ((1 - ε) * Λ) (d₀ + s * d) (cost p) :=
  (h p a Λ d₀ hp ha haΛ hΛ habsolute X hX N hN f hf hfree d A hA
    (relativePatchDistinctWeights_le_degree A) hscore).prescribed_discount
      hτ (((Real.exp_pos (-p)).le.trans ha).trans haΛ) (le_refl s) hbudget

end Erdos3

end

end OAI
