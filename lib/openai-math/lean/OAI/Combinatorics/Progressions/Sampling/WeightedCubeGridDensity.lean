import OAI.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def gridBlockTailBudget (M j b : ℕ) (Q H : ℕ → ℕ) (ζ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m,
    (((Q (i + 1) + 1 : ℝ) * (2 * Q (i + 1) * (H (i + 1) + 1) + 1) *
      (2 * H (i + 1) + 1)) ^ j) * (ζ i) ^ b) + (M : ℝ) ^ j * (ζ m) ^ b

noncomputable def weightedCubeGridApproximation {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift z : J → ℤ) (S : Finset (J → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ J.card * ∑ k ∈ S, (∏ b, weightedCubeGridCoefficient (s b) M J k) *
    (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))

theorem weightedCubeGridDensity_fourier {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (shift z : J → ℤ) :
    (integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) K M z : ℂ) =
      weightedCubeGridApproximation s K M J shift z Finset.univ := by
  rw [integerGridDensity_fourier]
  simp only [weightedCubeGridApproximation, Fintype.card_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedCubeIntegerJetSum_coefficient]
  ring

theorem weightedCubeGridDensity_truncation {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U : ℝ}
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (ζ : ℕ → ℝ) (m : ℕ) (hζ : ∀ i ≤ m, 0 < ζ i ∧ ζ i ≤ 1)
    (hlen : ∀ i ≤ m, ∀ b j, localizedMajorArcLengthBudget n U (ζ i) ≤ (s b j).length)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (Q H : ℕ → ℕ)
    (hQ : ∀ i ≤ m, (localizedMajorArcBudget n U (ζ i) * U ^ (n + 1)) ^ J.card ≤ Q i)
    (hH : ∀ i ≤ m, ∀ b, M * (localizedMajorArcErrorBudget n U (ζ i) /
      ∏ j, ((s b j).length : ℝ)) ≤ H i)
    (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) K M z : ℂ) -
        weightedCubeGridApproximation s K M J shift z (rationalGridMajorBox J M (Q 0) (H 0))‖ ≤
      ((K : ℝ) / M) ^ J.card * gridBlockTailBudget M J.card (Fintype.card B) Q H ζ m := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hb := weightedCubeGridProduct_truncation_le s A hA h ζ m hζ hlen hM J hJ Q H hQ hH ψ hψ
  rw [weightedCubeGridDensity_fourier]
  unfold weightedCubeGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem weightedCubeGridDensity_eq_pointMass {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) (K M : ℕ)
    (J : Finset (Finset I)) (shift z : J → ℤ)
    (hM : ∀ S : J, 2 * weightedCubeJetBound s S < (M : ℤ))
    (hz : ∀ S : J, |z S - shift S| ≤ weightedCubeJetBound s S) :
    integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) K M z =
      (K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) z := by
  simp only [integerGridDensity, Fintype.card_coe, weightedCubeIntegerGridMass_eq s J shift z M hM hz]

end Erdos3

end

end OAI
