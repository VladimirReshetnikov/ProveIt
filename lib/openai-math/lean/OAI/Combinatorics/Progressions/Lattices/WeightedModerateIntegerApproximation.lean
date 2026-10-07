import OAI.Combinatorics.Progressions.Estimates.WeightedCubePlateau
import OAI.Combinatorics.Progressions.Estimates.WeightedRetainedCoefficients

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCube_integer_density_approximation {B I : Type*}
    [Fintype B] [Nonempty B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} [NeZero K] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V D E ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hupper : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (hlower : ∀ b, (K : ℝ) ≤ D * ∏ j, ((s b j).length : ℝ))
    (p : ℕ) (hpower : ∀ b j, (K : ℝ) ≤ E * ((s b j).length : ℝ) ^ p)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ Fintype.card B) :
    let R := blockTorusFactor (Fintype.card I) (n + 1) (Fintype.card B) V
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) (R * K) J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ T, |ξ T| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ T, ((k T).val : ℝ) / (R * K) = (a T : ℝ) / d + ξ T / K) ∧
      ∀ shift z : J → ℤ,
        (∀ T, |(z T : ℝ) - shift T| ≤ blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V * K) →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
            (weightedCubeIntegerJetSum s J shift) z : ℝ) : ℂ) -
          weightedCubeGridApproximation s K (R * K) J shift z S‖ ≤ ε := by
  let R := blockTorusFactor (Fintype.card I) (n + 1) (Fintype.card B) V
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hR : 0 < R := blockTorusFactor_pos _ _ _ _
  obtain ⟨m, hm, hmin, hsize⟩ := exists_scaled_grid_minimum
    (fun x : B × Fin (n + 1) => (s x.1 x.2).length)
    (fun x => (s x.1 x.2).length_pos) (R := R) p J.card (fun x => hpower x.1 x.2)
  have hVD : 0 ≤ (R : ℝ) * D := by positivity
  have hWE : 0 ≤ ((R : ℝ) * E) ^ J.card := by positivity
  have hscale (b : B) : ((R * K : ℕ) : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ (R : ℝ) * D := by
    have hp : 0 < ∏ j, ((s b j).length : ℝ) :=
      Finset.prod_pos (fun j _ => by exact_mod_cast (s b j).length_pos)
    simpa only [Nat.cast_mul] using scaled_grid_volume_bound (Nat.cast_nonneg R) hp (hlower b)
  let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
  let S := uniformBlockSpectrumCover J (R * K) n U ((R : ℝ) * D) (m : ℝ) ζ
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · simpa only [S, ζ, Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card
      J (R * K) n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hε hε1
      (by simpa only [Fintype.card_coe] using hsize)
  · exact weightedCube_uniform_absolute_cap s A hA hU hVD hWE (Nat.cast_nonneg m) h
      (fun b j => by exact_mod_cast hmin (b, j)) (R * K) (p * J.card) (Nat.mul_pos hR hK) J hJ hB hsize hscale
  · intro k hk
    obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n J.card (p * J.card) hU hWE hε
    obtain ⟨d, hd, hdb, a, ξ, hξ, he⟩ := uniformBlockSpectrumCover_character (Nat.mul_pos hR hK)
      n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hζ hζ1
      (by simpa only [Fintype.card_coe] using hsize) k hk
    obtain ⟨ρ, hρ, hρe⟩ := grid_character_rescale hR k a ξ hξ (by simpa only [Nat.cast_mul] using he)
    refine ⟨d, hd, ?_, a, ρ, ?_, hρe⟩
    · simpa only [Fintype.card_coe] using hdb
    · simpa only [Fintype.card_coe] using hρ
  · have hd := (weightedCube_uniform_grid_density s A hA hU hVD hWE (Nat.cast_nonneg m) hε h
      (fun b j => by exact_mod_cast hmin (b, j)) K (R * K) (p * J.card) J hJ hB hsize hscale).2
    intro shift z hz
    have he : integerGridDensity (weightedCubeIntegerSource s) (weightedCubeIntegerJetSum s J shift)
        K (R * K) z = (K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
          (weightedCubeIntegerJetSum s J shift) z := by
      unfold integerGridDensity
      rw [weightedCube_grid_mass_eq_torus s hV hK hupper J hJ shift z hz, Fintype.card_coe]
    have ht := hd shift z
    rw [he] at ht
    apply ht.trans
    have hf := grid_scale_factor_le_one R K J.card hR hK
    have hh := mul_le_mul_of_nonneg_right hf hε.le
    simpa only [Nat.cast_mul, one_mul] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedModerate_integer_density_approximation {B I : Type*}
    [Fintype B] [Nonempty B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} [NeZero K] (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V D E ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hupper : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (hlower : ∀ b, (K : ℝ) ≤ D * ((c b).length * ∏ j, ((s b j).length : ℝ)))
    (p : ℕ) (hpower : ∀ b j, (K : ℝ) ≤ E * ((s b j).length : ℝ) ^ p)
    (hcpower : ∀ b, (K : ℝ) ≤ E * ((c b).length : ℝ) ^ p)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ Fintype.card B) :
    let R := blockTorusFactor (Fintype.card I) n (Fintype.card B) V
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) (R * K) J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ T, |ξ T| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ T, ((k T).val : ℝ) / (R * K) = (a T : ℝ) / d + ξ T / K) ∧
      ∀ shift z : J → ℤ,
        (∀ T, |(z T : ℝ) - shift T| ≤ blockJetScaleBound (Fintype.card I) n (Fintype.card B) V * K) →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
            (weightedModerateIntegerJetSum c s J offset shift) z : ℝ) : ℂ) -
          weightedModerateGridApproximation c s K (R * K) J offset shift z S‖ ≤ ε := by
  let R := blockTorusFactor (Fintype.card I) n (Fintype.card B) V
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hR : 0 < R := blockTorusFactor_pos _ _ _ _
  let length (x : B × Option (Fin n)) : ℕ := x.2.elim (c x.1).length (fun j => (s x.1 j).length)
  have hpos (x : B × Option (Fin n)) : 0 < length x := by
    rcases x with ⟨b, _ | j⟩
    · exact (c b).length_pos
    · exact (s b j).length_pos
  have hpow (x : B × Option (Fin n)) : (K : ℝ) ≤ E * (length x : ℝ) ^ p := by
    rcases x with ⟨b, _ | j⟩
    · exact hcpower b
    · exact hpower b j
  obtain ⟨m, hm, hmin, hsize⟩ := exists_scaled_grid_minimum length hpos (R := R) p J.card hpow
  have hVD : 0 ≤ (R : ℝ) * D := by positivity
  have hWE : 0 ≤ ((R : ℝ) * E) ^ J.card := by positivity
  have hscale (b : B) : ((R * K : ℕ) : ℝ) /
      ((((c b).modulus none : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ)) ≤ (R : ℝ) * D := by
    have hp : 0 < (((c b).modulus none : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ) := by
      apply mul_pos
      · exact mul_pos (by exact_mod_cast (c b).modulus_pos none) (by exact_mod_cast (c b).length_pos)
      · exact Finset.prod_pos (fun j _ => by exact_mod_cast (s b j).length_pos)
    simpa only [Nat.cast_mul] using scaled_grid_volume_bound (Nat.cast_nonneg R) hp
      (weightedModerate_physical_volume_lower (c b) (s b) hD (hlower b))
  let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
  let S := uniformBlockSpectrumCover J (R * K) n U ((R : ℝ) * D) (m : ℝ) ζ
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · simpa only [S, ζ, Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card
      J (R * K) n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hε hε1
      (by simpa only [Fintype.card_coe] using hsize)
  · exact weightedModerate_uniform_absolute_cap c s (fun b => (offset b : ℝ)) A hA hU hVD hWE
      (Nat.cast_nonneg m) hc h (fun b => by exact_mod_cast hmin (b, none))
      (fun b j => by exact_mod_cast hmin (b, some j)) (R * K) (p * J.card) (Nat.mul_pos hR hK)
      J hJ hB hsize hscale
  · intro k hk
    obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n J.card (p * J.card) hU hWE hε
    obtain ⟨d, hd, hdb, a, ξ, hξ, he⟩ := uniformBlockSpectrumCover_character (Nat.mul_pos hR hK)
      n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hζ hζ1
      (by simpa only [Fintype.card_coe] using hsize) k hk
    obtain ⟨ρ, hρ, hρe⟩ := grid_character_rescale hR k a ξ hξ (by simpa only [Nat.cast_mul] using he)
    refine ⟨d, hd, ?_, a, ρ, ?_, hρe⟩
    · simpa only [Fintype.card_coe] using hdb
    · simpa only [Fintype.card_coe] using hρ
  · have hd := (weightedModerate_uniform_grid_density c s offset A hA hU hVD hWE (Nat.cast_nonneg m)
      hε hc h (fun b => by exact_mod_cast hmin (b, none))
      (fun b j => by exact_mod_cast hmin (b, some j)) K (R * K) (p * J.card) J hJ hB hsize hscale).2
    intro shift z hz
    have he : integerGridDensity (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset shift) K (R * K) z =
        (K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
          (weightedModerateIntegerJetSum c s J offset shift) z := by
      unfold integerGridDensity
      rw [weightedModerate_grid_mass_eq_torus c s offset hV hK hupper J hJ shift z hz, Fintype.card_coe]
    have ht := hd shift z
    rw [he] at ht
    apply ht.trans
    have hf := grid_scale_factor_le_one R K J.card hR hK
    have hh := mul_le_mul_of_nonneg_right hf hε.le
    simpa only [Nat.cast_mul, one_mul] using hh

end Erdos3

end

end OAI
