import OAI.Combinatorics.Progressions.Sampling.WeightedUniformGridDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCube_uniform_absolute_cap {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖) ≤ uniformSpectrumAbsoluteCap n J.card t U V W := by
  rw [← Fintype.card_coe]
  apply uniformBlockSpectrum_absolute_cap M n t (fun b => weightedCubeGridCoefficient (s b) M J) hU hV hW hL
    (by simpa only [Fintype.card_coe] using hB) (by simpa only [Fintype.card_coe] using hsize)
  · exact fun b k => weightedCubeGridCoefficient_norm_le_one (s b) M J k
  · intro δ hδ hδ1 hlength b k hk
    exact weightedCubeGridCoefficient_minor_polynomial (s b) A hA (h b) hV hδ hδ1
      (fun j => hlength.trans (hlen b j)) hM (hscale b) J hJ k
      (by simpa only [Fintype.card_coe] using hk)

theorem weightedModerate_uniform_absolute_cap {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℝ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ((((c b).modulus none : ℝ) * (c b).length) *
      ∏ j, ((s b j).length : ℝ)) ≤ V) :
    (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b) M J k‖) ≤
      uniformSpectrumAbsoluteCap n J.card t U V W := by
  rw [← Fintype.card_coe]
  apply uniformBlockSpectrum_absolute_cap M n t
    (fun b => weightedModerateGridCoefficient (c b) (s b) (offset b) M J) hU hV hW hL
    (by simpa only [Fintype.card_coe] using hB) (by simpa only [Fintype.card_coe] using hsize)
  · exact fun b k => weightedModerateGridCoefficient_norm_le_one (c b) (s b) (offset b) M J k
  · intro δ hδ hδ1 hlength b k hk
    exact weightedModerateGridCoefficient_minor_polynomial (c b) (s b) A hA (hc b) (h b)
      hV hδ hδ1 (hlength.trans (hclen b)) (fun j => hlength.trans (hlen b j)) (offset b)
      hM (hscale b) J hJ k (by simpa only [Fintype.card_coe] using hk)

theorem weightedCube_grid_density_bound {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖) ≤ C)
    (shift z : J → ℤ) :
    integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift) K M z ≤
      ((K : ℝ) / M) ^ J.card * C := by
  have ht := integerGridDensity_absolute_cap (weightedCubeIntegerSource s)
    (weightedCubeIntegerJetSum s J shift) K M z
  simp only [Fintype.card_coe, weightedCubeIntegerJetSum_coefficient, norm_mul,
    rectangularGridCharacter_norm, one_mul] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hcap (by positivity))

theorem weightedModerate_grid_density_bound {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k‖) ≤ C)
    (shift z : J → ℤ) :
    integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift) K M z ≤ ((K : ℝ) / M) ^ J.card * C := by
  have ht := integerGridDensity_absolute_cap (weightedModerateIntegerProductSource c s)
    (weightedModerateIntegerJetSum c s J offset shift) K M z
  simp only [Fintype.card_coe, weightedModerateIntegerJetSum_coefficient, norm_mul,
    rectangularGridCharacter_norm, one_mul] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hcap (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def weightedCubeRetainedCoefficient {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (center : J → ℤ) (k : J → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ J.card * (∏ b, weightedCubeGridCoefficient (s b) M J k) * rectangularGridCharacter M k center

theorem weightedCubeGridApproximation_eq_sum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (center z : J → ℤ) (S : Finset (J → Fin M)) :
    weightedCubeGridApproximation s K M J center z S =
      ∑ k ∈ S, weightedCubeRetainedCoefficient s K M J center k * star (rectangularGridCharacter M k z) := by
  rw [weightedCubeGridApproximation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold weightedCubeRetainedCoefficient
  ring

theorem weightedCubeRetainedCoefficient_norm {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (center : J → ℤ) (k : J → Fin M) :
    ‖weightedCubeRetainedCoefficient s K M J center k‖ =
      ((K : ℝ) / M) ^ J.card * ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖ := by
  simp only [weightedCubeRetainedCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, rectangularGridCharacter_norm, mul_one]

theorem weightedCubeRetainedCoefficient_mass {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (center : J → ℤ) (S : Finset (J → Fin M))
    {C : ℝ} (hC : (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖) ≤ C) :
    (∑ k ∈ S, ‖weightedCubeRetainedCoefficient s K M J center k‖) ≤ ((K : ℝ) / M) ^ J.card * C := by
  classical
  simp only [weightedCubeRetainedCoefficient_norm, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (finite_product_retained_mass_le _ S hC) (by positivity)

noncomputable def weightedModerateRetainedCoefficient {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (center : J → ℤ) (k : J → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ J.card * (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k) *
    rectangularGridCharacter M k center

theorem weightedModerateGridApproximation_eq_sum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (center z : J → ℤ) (S : Finset (J → Fin M)) :
    weightedModerateGridApproximation c s K M J offset center z S =
      ∑ k ∈ S, weightedModerateRetainedCoefficient c s K M J offset center k *
        star (rectangularGridCharacter M k z) := by
  rw [weightedModerateGridApproximation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold weightedModerateRetainedCoefficient
  ring

theorem weightedModerateRetainedCoefficient_norm {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (center : J → ℤ) (k : J → Fin M) :
    ‖weightedModerateRetainedCoefficient c s K M J offset center k‖ =
      ((K : ℝ) / M) ^ J.card * ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k‖ := by
  simp only [weightedModerateRetainedCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, rectangularGridCharacter_norm, mul_one]

theorem weightedModerateRetainedCoefficient_mass {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (center : J → ℤ) (S : Finset (J → Fin M))
    {C : ℝ} (hC : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M J k‖) ≤ C) :
    (∑ k ∈ S, ‖weightedModerateRetainedCoefficient c s K M J offset center k‖) ≤
      ((K : ℝ) / M) ^ J.card * C := by
  classical
  simp only [weightedModerateRetainedCoefficient_norm, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (finite_product_retained_mass_le _ S hC) (by positivity)

end Erdos3

end

end OAI
