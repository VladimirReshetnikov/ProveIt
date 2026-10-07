import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem RelativePatchPowerInductionRule.of_mean_increment
    {s n₀ E d₀ : ℕ} {τ p a Λ : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    (hX : (Fintype.card X : ℝ) ≤ p)
    (N : X → ℕ) (hN : ∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : 2 * a ≤ 𝔼 x ∈ integerBox N, f x) :
    RelativePatchSliceConclusion s N f ((1 - τ) ^ (s + 1) * Λ) d₀ ((p + 2) ^ E) := by
  let A := PolynomialPatch.constant X s 1 (by constructor <;> norm_num)
  have hval (t : X → ℝ) : A.value t = 1 := PolynomialPatch.constant_value _ _ t
  have hbox : (integerBox N).Nonempty := by
    refine ⟨0, (mem_integerBox N _).mpr (fun i => ⟨le_rfl, ?_⟩)⟩
    have hi : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
    change (0 : ℤ) < N i
    exact_mod_cast hi
  have hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a A := by
    simp only [relativePatchBoxScore, hval, mul_one,
      Finset.expect_sub_distrib, Finset.expect_const hbox]
    linarith
  have hcomp : relativePatchComplexity A ≤ p := by
    have hlip : A.kernel.lip = 0 := PolynomialPatch.constant_lip _ _
    rw [relativePatchComplexity, hlip]
    norm_num only [NNReal.coe_zero, Nat.cast_zero, add_zero, zero_add, Real.log_one]
    linarith
  have hstage : relativePatchDistinctWeights A ≤ s := by
    rw [(relativePatchDistinctWeights_eq_zero_iff A).mpr rfl]
    exact Nat.zero_le _
  simpa only [Nat.mul_zero, Nat.add_zero] using hrelative p a Λ d₀ hp ha haΛ hΛ habsolute
    X hX N hN f hf hfree 0 A hcomp hstage hscore

end Erdos3

end

end OAI
