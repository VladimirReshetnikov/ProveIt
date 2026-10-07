import OAI.Combinatorics.Progressions.Estimates.FiniteWeightedExpansion
import OAI.Combinatorics.Progressions.Fourier.AffineUniformSpectrum
import OAI.Combinatorics.Progressions.Probability.WeightedPlateauMixture
import OAI.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def integerGridApproximation {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ℤ) : ℂ :=
  ((K : ℂ) / M) ^ Fintype.card J * ∑ k ∈ S, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)

theorem affine_weightedCube_grid_density {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    ∀ shift z, ‖(integerGridDensity (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
      K M z : ℂ) - integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
        K M S z‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  dsimp only
  have ht := (affine_weightedCube_uniform_spectrum s (fun b j i => (u b j i : ℝ)) v A hA hU hV hW hL hε
    h hlen hv hstride M t (Nat.pos_of_ne_zero (NeZero.ne M)) J hJ hB hsize hscale).1
  intro shift z
  have he := integerGridDensity_truncation (weightedCubeIntegerSource s)
    (affineWeightedCubeIntegerSum s u v J shift) K M
      (uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n J.card t U V W ε)) z
  have htail : spectrumTail (uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n J.card t U V W ε))
      (fun k => ‖integerGridCoefficient (weightedCubeIntegerSource s)
        (affineWeightedCubeIntegerSum s u v J shift) M k‖) ≤ ε := by
    simpa only [affineWeightedCubeIntegerSum_coefficient, norm_mul, rectangularGridCharacter_norm, one_mul] using ht
  simpa only [integerGridApproximation, Fintype.card_coe] using
    he.trans (mul_le_mul_of_nonneg_left htail (by positivity))

theorem affine_weightedModerate_grid_density {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U) (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (ht : ∀ b, 0 < stride b) (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hcoeff : ∀ b, ((stride b * (c b).modulus none : ℕ) : ℝ) ≤ U)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ((((stride b * (c b).modulus none : ℕ) : ℝ) * (c b).length) *
      ∏ j, ((s b j).length : ℝ)) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    ∀ shift z, ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
      (affineWeightedModerateIntegerSum c s offset stride u v J shift) K M z : ℂ) -
        integerGridApproximation (weightedModerateIntegerProductSource c s)
          (affineWeightedModerateIntegerSum c s offset stride u v J shift) K M S z‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  dsimp only
  have htail := (affine_weightedModerate_uniform_spectrum c s (fun b => (offset b : ℝ)) stride
    (fun b j i => (u b j i : ℝ)) v A hA hU hV hW hL hε hc h hclen hlen ht hv hstride hcoeff M t
    (Nat.pos_of_ne_zero (NeZero.ne M)) J hJ hB hsize hscale).1
  intro shift z
  have he := integerGridDensity_truncation (weightedModerateIntegerProductSource c s)
    (affineWeightedModerateIntegerSum c s offset stride u v J shift) K M
      (uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n J.card t U V W ε)) z
  have hb : spectrumTail (uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n J.card t U V W ε))
      (fun k => ‖integerGridCoefficient (weightedModerateIntegerProductSource c s)
        (affineWeightedModerateIntegerSum c s offset stride u v J shift) M k‖) ≤ ε := by
    simpa only [affineWeightedModerateIntegerSum_coefficient, norm_mul, rectangularGridCharacter_norm, one_mul] using htail
  simpa only [integerGridApproximation, Fintype.card_coe] using
    he.trans (mul_le_mul_of_nonneg_left hb (by positivity))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
variable (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)

noncomputable def affineCubePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v rows shift) K M F z

theorem affineCubePlateauApproximation_split
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    affineCubePlateauApproximation s u v K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k) *
          (rationalGridPhase (D k) (a k) (integerGridResidue (D k) (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold affineCubePlateauApproximation integerGridApproximation
  simp only [Fintype.card_coe, affineWeightedCubeIntegerSum_coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

theorem affineCubePlateauMixture_expansion
    {T : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I))
    (shift : T → rows → ℤ) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    (∫ zeta, affineCubePlateauApproximation s u v K H rows (shift zeta) z F ∂p.toMeasure) =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K)) := by
  simp_rw [affineCubePlateauApproximation_split s u v hK H rows _ z F D a ω hfreq]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, plateauModeMixture_grid_factor]
  · intro k _
    apply Integrable.const_mul
    apply pmf_integrable_of_norm_le p _ (B := 1)
    intro zeta
    rw [norm_mul, rationalGridPhase_norm, one_mul]
    exact plateauFourierMode_norm _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_fundamental_approximation {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n K Q : ℕ} [NeZero K]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (t : ℕ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hQ : ∀ S : J, affineWeightedCubeJetBound s u v S ≤ (Q : ℤ) * K)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (((2 * Q + 1) * K : ℕ) : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (((2 * Q + 1) * K : ℕ) : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J ((2 * Q + 1) * K) n U V L ζ
    ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
      ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
        (affineWeightedCubeIntegerSum s u v J center) z : ℝ) : ℂ) -
          integerGridApproximation (weightedCubeIntegerSource s)
            (affineWeightedCubeIntegerSum s u v J center) K ((2 * Q + 1) * K) S z‖ ≤ ε := by
  dsimp only
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hd := affine_weightedCube_grid_density s u v A hA hU hV hW hL hε h hlen hv hstride
    K ((2 * Q + 1) * K) t J hJ hB hsize hscale
  intro center z hz
  have he : integerGridDensity (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J center)
      K ((2 * Q + 1) * K) z = (K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
        (affineWeightedCubeIntegerSum s u v J center) z := by
    unfold integerGridDensity
    rw [affineWeightedCube_mass_on_fundamental_box s u v hK J hQ center z hz, Fintype.card_coe]
  have ht := hd center z
  rw [he] at ht
  apply ht.trans
  have hf := mul_le_mul_of_nonneg_right (grid_scale_factor_le_one (2 * Q + 1) K J.card (by omega) hK) hε.le
  simpa only [Nat.cast_mul, one_mul] using hf

theorem affine_weightedModerate_fundamental_approximation {B I : Type*}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n K Q : ℕ} [NeZero K]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U) (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (ht : ∀ b, 0 < stride b) (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hcoeff : ∀ b, ((stride b * (c b).modulus none : ℕ) : ℝ) ≤ U)
    (t : ℕ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hQ : ∀ S : J, affineWeightedModerateJetBound c s offset stride u v S ≤ (Q : ℤ) * K)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (((2 * Q + 1) * K : ℕ) : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (((2 * Q + 1) * K : ℕ) : ℝ) /
      ((((stride b * (c b).modulus none : ℕ) : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ)) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J ((2 * Q + 1) * K) n U V L ζ
    ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
      ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
        (affineWeightedModerateIntegerSum c s offset stride u v J center) z : ℝ) : ℂ) -
          integerGridApproximation (weightedModerateIntegerProductSource c s)
            (affineWeightedModerateIntegerSum c s offset stride u v J center)
              K ((2 * Q + 1) * K) S z‖ ≤ ε := by
  dsimp only
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hd := affine_weightedModerate_grid_density c s offset stride u v A hA hU hV hW hL hε
    hc h hclen hlen ht hv hstride hcoeff K ((2 * Q + 1) * K) t J hJ hB hsize hscale
  intro center z hz
  have he : integerGridDensity (weightedModerateIntegerProductSource c s)
      (affineWeightedModerateIntegerSum c s offset stride u v J center) K ((2 * Q + 1) * K) z =
        (K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
          (affineWeightedModerateIntegerSum c s offset stride u v J center) z := by
    unfold integerGridDensity
    rw [affineWeightedModerate_mass_on_fundamental_box c s offset stride u v hK J hQ center z hz,
      Fintype.card_coe]
  have he' := hd center z
  rw [he] at he'
  apply he'.trans
  have hf := mul_le_mul_of_nonneg_right (grid_scale_factor_le_one (2 * Q + 1) K J.card (by omega) hK) hε.le
  simpa only [Nat.cast_mul, one_mul] using hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerRetainedCoefficient {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (k : J → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ Fintype.card J * integerGridCoefficient p Y M k

theorem integerRetainedCoefficient_norm {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (k : J → Fin M) :
    ‖integerRetainedCoefficient p Y K M k‖ =
      ((K : ℝ) / M) ^ Fintype.card J * ‖integerGridCoefficient p Y M k‖ := by
  simp only [integerRetainedCoefficient, norm_mul, norm_pow, norm_div, Complex.norm_natCast]

theorem integerGridApproximation_eq_sum {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) (z : J → ℤ) :
    integerGridApproximation p Y K M S z =
      ∑ k ∈ S, integerRetainedCoefficient p Y K M k * star (rectangularGridCharacter M k z) := by
  simp only [integerGridApproximation, integerRetainedCoefficient, Finset.mul_sum, mul_assoc]

theorem integerRetainedCoefficient_mass {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) {C : ℝ}
    (hC : (∑ k, ‖integerGridCoefficient p Y M k‖) ≤ C) :
    (∑ k ∈ S, ‖integerRetainedCoefficient p Y K M k‖) ≤ ((K : ℝ) / M) ^ Fintype.card J * C := by
  classical
  simp only [integerRetainedCoefficient_norm, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.sum_le_univ_sum_of_nonneg (s := S) (fun _ => norm_nonneg _)).trans hC

theorem integerRetainedCoefficient_mass_le {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) {C : ℝ} (hKM : K ≤ M)
    (hC : (∑ k, ‖integerGridCoefficient p Y M k‖) ≤ C) :
    (∑ k ∈ S, ‖integerRetainedCoefficient p Y K M k‖) ≤ C := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hratio : (K : ℝ) / M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast hKM)
  have hpow : ((K : ℝ) / M) ^ Fintype.card J ≤ 1 := pow_le_one₀ (by positivity) hratio
  have hnonneg : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hC
  exact (integerRetainedCoefficient_mass p Y K M S hC).trans (mul_le_of_le_one_left hnonneg hpow)

theorem integerGridApproximation_norm_le {X J : Type*} [Fintype X] [Fintype J]
    [DecidableEq J] (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) (z : J → ℤ) {C : ℝ} (hKM : K ≤ M)
    (hC : (∑ k, ‖integerGridCoefficient p Y M k‖) ≤ C) :
    ‖integerGridApproximation p Y K M S z‖ ≤ C := by
  rw [integerGridApproximation_eq_sum]
  exact retainedExpansion_norm_bound S (integerRetainedCoefficient p Y K M)
    (fun k w => star (rectangularGridCharacter M k w)) z
    (integerRetainedCoefficient_mass_le p Y K M S hKM hC)
    (fun k _ => by rw [norm_star, rectangularGridCharacter_norm])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def progressionCubeSources {b g : ℕ} (q : ℕ)
    (m H : Fin b → Fin g → ℕ) (c : Fin b → Fin g → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j) :
    Fin b → Fin g → NormalizedScalarCubeSource (Fin q) :=
  fun a j => normalizedProgressionCubeSource q (m a j) (H a j) (c a j) (hL a j) (hm a j) (hsize a j)

noncomputable def progressionCubeBlockWeights {b g : ℕ} (q : ℕ)
    (m H : Fin b → Fin g → ℕ) (c : Fin b → Fin g → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j) :
    FiniteProbabilityWeights (∀ a j, SupportedCube q (integerProgressionSupport (c a j) (m a j : ℤ) (H a j) : Set ℤ)) :=
  FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
    uniformProgressionCubeWeights q (m a j) (H a j) (c a j) (hL a j) (hm a j)))

noncomputable def progressionCubeIntegerSum {b g : ℕ} (q : ℕ)
    (m H : Fin b → Fin g → ℕ) (c : Fin b → Fin g → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (x : ∀ a j, SupportedCube q (integerProgressionSupport (c a j) (m a j : ℤ) (H a j) : Set ℤ)) : J → ℤ :=
  center + ∑ a, fun Z : J => integerBooleanBlockJet (fun j => supportedCubeCoordinates (x a j).val) Z

theorem progressionCubeIntegerSum_mass {b n : ℕ} (q : ℕ)
    (m H : Fin b → Fin (n + 1) → ℕ) (c : Fin b → Fin (n + 1) → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (J : Finset (Finset (Fin q))) (center z : J → ℤ) :
    finiteImageMass (weightedCubeIntegerSource (progressionCubeSources q m H c hL hm hsize))
      (affineWeightedCubeIntegerSum (progressionCubeSources q m H c hL hm hsize)
        (fun a j => cubeRootOffset (c a j)) (fun _ _ _ => 1) J center) z =
      finiteImageMass (progressionCubeBlockWeights q m H c hL hm) (progressionCubeIntegerSum q m H c J center) z := by
  exact progressionCubeBlocks_imageMass q m H c hL hm hsize
    (fun x => center + ∑ a, fun Z : J => integerBooleanBlockJet (x a) Z) z

theorem progressionCubeIntegerSum_coefficient {b n : ℕ} (q : ℕ)
    (m H : Fin b → Fin (n + 1) → ℕ) (c : Fin b → Fin (n + 1) → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (weightedCubeIntegerSource (progressionCubeSources q m H c hL hm hsize))
      (affineWeightedCubeIntegerSum (progressionCubeSources q m H c hL hm hsize)
        (fun a j => cubeRootOffset (c a j)) (fun _ _ _ => 1) J center) M k =
      integerGridCoefficient (progressionCubeBlockWeights q m H c hL hm)
        (progressionCubeIntegerSum q m H c J center) M k := by
  exact progressionCubeBlocks_complexMean q m H c hL hm hsize
    (fun x => rectangularGridCharacter M k (center + ∑ a, fun Z : J => integerBooleanBlockJet (x a) Z))

theorem progressionCubeIntegerSum_approximation {b n : ℕ} (q : ℕ)
    (m H : Fin b → Fin (n + 1) → ℕ) (c : Fin b → Fin (n + 1) → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (J : Finset (Finset (Fin q))) (center z : J → ℤ) (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) :
    integerGridApproximation (weightedCubeIntegerSource (progressionCubeSources q m H c hL hm hsize))
      (affineWeightedCubeIntegerSum (progressionCubeSources q m H c hL hm hsize)
        (fun a j => cubeRootOffset (c a j)) (fun _ _ _ => 1) J center) K M S z =
      integerGridApproximation (progressionCubeBlockWeights q m H c hL hm)
        (progressionCubeIntegerSum q m H c J center) K M S z := by
  unfold integerGridApproximation
  simp only [progressionCubeIntegerSum_coefficient]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def weightedSliceIntegerSource {b g q : ℕ}
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin g → ℤ) :
    FiniteProbabilityWeights (∀ a j, (s a j).SliceDomain (root a j)) :=
  FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).sliceWeights (root a j)))

noncomputable def weightedSliceIntegerSum {b g q : ℕ}
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin g → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (x : ∀ a j, (s a j).SliceDomain (root a j)) : J → ℤ :=
  center + ∑ a, fun Z : J => integerBooleanBlockJet (fun j => supportedCubeCoordinates (x a j).val.val) Z

theorem weightedSliceIntegerSum_complexMean {b n q : ℕ}
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (f : (J → ℤ) → ℂ) :
    (weightedCubeIntegerSource s).complexMean (fun x => f (affineWeightedCubeIntegerSum s
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center x)) =
      (weightedSliceIntegerSource s root).complexMean (fun x => f (weightedSliceIntegerSum s root J center x)) := by
  have he := weightedSliceBlocks_complexMean s root
    (fun x => f (center + ∑ a, fun Z : J => integerBooleanBlockJet (x a) Z))
  unfold weightedCubeIntegerSource affineWeightedCubeIntegerSum affineWeightedCubeIntegerBlock
    weightedSliceIntegerSource weightedSliceIntegerSum
  simpa only [affineIntegerCubeCoordinates_root] using he

theorem weightedSliceIntegerSum_mass {b n q : ℕ}
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (J : Finset (Finset (Fin q))) (center z : J → ℤ) :
    finiteImageMass (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) z =
      finiteImageMass (weightedSliceIntegerSource s root) (weightedSliceIntegerSum s root J center) z :=
  finiteImageMass_eq_of_complexMean _ _ _ _ (weightedSliceIntegerSum_complexMean s root J center) z

theorem weightedSliceIntegerSum_coefficient {b n q : ℕ}
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) M k =
      integerGridCoefficient (weightedSliceIntegerSource s root) (weightedSliceIntegerSum s root J center) M k :=
  weightedSliceIntegerSum_complexMean s root J center (rectangularGridCharacter M k)

theorem weightedSliceIntegerSum_approximation {b n q : ℕ}
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (J : Finset (Finset (Fin q))) (center z : J → ℤ) (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) :
    integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) K M S z =
      integerGridApproximation (weightedSliceIntegerSource s root) (weightedSliceIntegerSum s root J center) K M S z := by
  unfold integerGridApproximation
  simp only [weightedSliceIntegerSum_coefficient]

noncomputable def moderateSliceIntegerSource {b g q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin g → ℤ) :
    FiniteProbabilityWeights (∀ a, (c a).CoefficientDomain × (∀ j, (s a j).SliceDomain (root a j))) :=
  FiniteProbabilityWeights.pi (fun a => moderateSliceWeights (c a) (s a) (root a))

noncomputable def moderateSliceIntegerSum {b g q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (root : Fin b → Fin g → ℤ) (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (x : ∀ a, (c a).CoefficientDomain × (∀ j, (s a j).SliceDomain (root a j))) : J → ℤ :=
  center + ∑ a, fun Z : J => (offset a + (stride a : ℤ) * (x a).1) *
    integerBooleanBlockJet (fun j => supportedCubeCoordinates ((x a).2 j).val.val) Z

theorem moderateSliceIntegerSum_complexMean {b n q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q)) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (root : Fin b → Fin n → ℤ) (J : Finset (Finset (Fin q))) (center : J → ℤ) (f : (J → ℤ) → ℂ) :
    (weightedModerateIntegerProductSource c s).complexMean (fun x => f (affineWeightedModerateIntegerSum c s
      offset stride (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center x)) =
      (moderateSliceIntegerSource c s root).complexMean
        (fun x => f (moderateSliceIntegerSum c s offset stride root J center x)) := by
  have he := moderateSliceBlocks_complexMean c s root (fun x => f (center + ∑ a,
    fun Z : J => (offset a + (stride a : ℤ) * (x a).1) * integerBooleanBlockJet (x a).2 Z))
  unfold weightedModerateIntegerProductSource weightedModerateIntegerSource
    affineWeightedModerateIntegerSum affineWeightedModerateIntegerBlock moderateSliceIntegerSource moderateSliceIntegerSum
  simpa only [affineIntegerCubeCoordinates_root] using he

theorem moderateSliceIntegerSum_mass {b n q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q)) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (root : Fin b → Fin n → ℤ) (J : Finset (Finset (Fin q))) (center z : J → ℤ) :
    finiteImageMass (weightedModerateIntegerProductSource c s) (affineWeightedModerateIntegerSum c s offset stride
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) z =
      finiteImageMass (moderateSliceIntegerSource c s root) (moderateSliceIntegerSum c s offset stride root J center) z :=
  finiteImageMass_eq_of_complexMean _ _ _ _ (moderateSliceIntegerSum_complexMean c s offset stride root J center) z

theorem moderateSliceIntegerSum_coefficient {b n q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q)) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (root : Fin b → Fin n → ℤ) (J : Finset (Finset (Fin q))) (center : J → ℤ)
    (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerProductSource c s) (affineWeightedModerateIntegerSum c s offset stride
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) M k =
      integerGridCoefficient (moderateSliceIntegerSource c s root)
        (moderateSliceIntegerSum c s offset stride root J center) M k :=
  moderateSliceIntegerSum_complexMean c s offset stride root J center (rectangularGridCharacter M k)

theorem moderateSliceIntegerSum_approximation {b n q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q)) (offset : Fin b → ℤ) (stride : Fin b → ℕ)
    (root : Fin b → Fin n → ℤ) (J : Finset (Finset (Fin q))) (center z : J → ℤ)
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) :
    integerGridApproximation (weightedModerateIntegerProductSource c s) (affineWeightedModerateIntegerSum c s offset stride
      (fun a j => cubeRootOffset (root a j)) (fun _ _ _ => 1) J center) K M S z =
      integerGridApproximation (moderateSliceIntegerSource c s root)
        (moderateSliceIntegerSum c s offset stride root J center) K M S z := by
  unfold integerGridApproximation
  simp only [moderateSliceIntegerSum_coefficient]

end Erdos3

end

end OAI
