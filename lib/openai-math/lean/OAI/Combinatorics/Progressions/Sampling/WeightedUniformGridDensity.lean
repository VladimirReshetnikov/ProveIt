import OAI.Combinatorics.Progressions.Fourier.WeightedModerateProductFourierTail
import OAI.Combinatorics.Progressions.Fourier.WeightedUniformSpectrumTail
import OAI.Combinatorics.Progressions.Lattices.WeightedModerateIntegerSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def weightedModerateGridApproximation {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ)
    (S : Finset (J → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ J.card * ∑ k ∈ S,
    (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k) *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))

theorem weightedModerateGridDensity_fourier {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ) :
    (integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift) K M z : ℂ) =
        weightedModerateGridApproximation c s K M J offset shift z Finset.univ := by
  rw [integerGridDensity_fourier]
  simp only [weightedModerateGridApproximation, Fintype.card_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedModerateIntegerJetSum_coefficient]
  ring

theorem weightedModerateGridDensity_truncation {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U : ℝ}
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (ζ : ℕ → ℝ) (m : ℕ) (hζ : ∀ i ≤ m, 0 < ζ i ∧ ζ i ≤ 1)
    (hclen : ∀ i ≤ m, ∀ b, localizedMajorArcLengthBudget n U (ζ i) ≤ (c b).length)
    (hlen : ∀ i ≤ m, ∀ b j, localizedMajorArcLengthBudget n U (ζ i) ≤ (s b j).length)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (Q H : ℕ → ℕ)
    (hQ : ∀ i ≤ m, ∀ b, (localizedMajorArcBudget n U (ζ i) * ((c b).modulus none * U ^ n)) ^ J.card ≤ Q i)
    (hH : ∀ i ≤ m, ∀ b, M * (localizedMajorArcErrorBudget n U (ζ i) /
      (((c b).modulus none * (c b).length : ℝ) * ∏ j, ((s b j).length : ℝ))) ≤ H i)
    (offset : B → ℤ) (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset shift) K M z : ℂ) -
      weightedModerateGridApproximation c s K M J offset shift z (rationalGridMajorBox J M (Q 0) (H 0))‖ ≤
      ((K : ℝ) / M) ^ J.card * gridBlockTailBudget M J.card (Fintype.card B) Q H ζ m := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hb := weightedModerateGridProduct_truncation_le c s A hA hc h ζ m hζ hclen hlen hM J hJ
    (fun b => (offset b : ℝ)) Q H hQ hH ψ hψ
  rw [weightedModerateGridDensity_fourier]
  unfold weightedModerateGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem weightedModerateGridDensity_eq_pointMass {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ)
    (hM : ∀ S : J, 2 * weightedModerateJetBound c s offset S < (M : ℤ))
    (hz : ∀ S : J, |z S - shift S| ≤ weightedModerateJetBound c s offset S) :
    integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift) K M z =
        (K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
          (weightedModerateIntegerJetSum c s J offset shift) z := by
  simp only [integerGridDensity, Fintype.card_coe, weightedModerateIntegerGridMass_eq c s J offset shift z M hM hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem weightedCubeGridDensity_error_of_tail {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (S : Finset (J → Fin M))
    {ε : ℝ} (htail : spectrumTail S (fun k => ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖) ≤ ε)
    (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) K M z : ℂ) -
      weightedCubeGridApproximation s K M J shift z S‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hb := (finite_series_truncation_le S
    (fun k => ∏ b, weightedCubeGridCoefficient (s b) M J k) ψ hψ).trans htail
  rw [weightedCubeGridDensity_fourier]
  unfold weightedCubeGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem weightedModerateGridDensity_error_of_tail {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (S : Finset (J → Fin M))
    {ε : ℝ} (htail : spectrumTail S (fun k =>
      ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k‖) ≤ ε)
    (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset shift) K M z : ℂ) -
      weightedModerateGridApproximation c s K M J offset shift z S‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hb := (finite_series_truncation_le S
    (fun k => ∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k) ψ hψ).trans htail
  rw [weightedModerateGridDensity_fourier]
  unfold weightedModerateGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCube_uniform_grid_density {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    (S.card : ℝ) ≤ uniformBlockSpectrumCardBudget n J.card t U V W ζ ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift)
            K M z : ℂ) - weightedCubeGridApproximation s K M J shift z S‖ ≤
          ((K : ℝ) / M) ^ J.card * ε := by
  dsimp only
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n J.card t hU hW hε
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.card_coe] using
      uniformBlockSpectrumCover_card J M n t hU hV hW hL hζ hζ1
        (by simpa only [Fintype.card_coe] using hsize)
  · have ht := weightedCube_uniform_spectrum_tail s A hA hU hV hW hL h hlen M t
      (Nat.pos_of_ne_zero (NeZero.ne M)) J hJ hB hsize hscale hζ hζ1 hε.le hacc
    intro shift z
    exact weightedCubeGridDensity_error_of_tail s K M J _ ht shift z

theorem weightedModerate_uniform_grid_density {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ((((c b).modulus none : ℝ) * (c b).length) *
      ∏ j, ((s b j).length : ℝ)) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    (S.card : ℝ) ≤ uniformBlockSpectrumCardBudget n J.card t U V W ζ ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
            (weightedModerateIntegerJetSum c s J offset shift) K M z : ℂ) -
          weightedModerateGridApproximation c s K M J offset shift z S‖ ≤
          ((K : ℝ) / M) ^ J.card * ε := by
  dsimp only
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n J.card t hU hW hε
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.card_coe] using
      uniformBlockSpectrumCover_card J M n t hU hV hW hL hζ hζ1
        (by simpa only [Fintype.card_coe] using hsize)
  · have ht := weightedModerate_uniform_spectrum_tail c s (fun b => (offset b : ℝ)) A hA
      hU hV hW hL hc h hclen hlen M t (Nat.pos_of_ne_zero (NeZero.ne M)) J hJ hB hsize hscale
      hζ hζ1 hε.le hacc
    intro shift z
    exact weightedModerateGridDensity_error_of_tail c s K M J offset _ ht shift z

end Erdos3

end

end OAI
