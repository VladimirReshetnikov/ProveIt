import OAI.Combinatorics.Progressions.Fourier.AffineTorusGeometry
import OAI.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def affinePrimitiveEnvelope (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M V : ℕ) : ℝ :=
  max 1 (max (scalarCubePrimitiveEnvelope I A B T M)
    (max (scalarCubePrimitiveEnvelope Empty A B T M) ((V * M : ℕ) : ℝ)))

theorem affinePrimitiveEnvelope_one_le (I : Type*) [Fintype I] (A B T : ℝ≥0) (M V : ℕ) :
    1 ≤ affinePrimitiveEnvelope I A B T M V := le_max_left _ _

theorem affinePrimitiveEnvelope_vector (I : Type*) [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M V : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (affinePrimitiveEnvelope I A B T M V) :=
  (scalarCubePrimitiveBudget_of_raw_bounds s A B T M hM hB hT).mono
    ((le_max_left _ _).trans (le_max_right _ _))

theorem affinePrimitiveEnvelope_coefficient (I : Type*) [Fintype I]
    (s : NormalizedScalarCubeSource Empty) (A B T : ℝ≥0) (M V : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (affinePrimitiveEnvelope I A B T M V) :=
  (scalarCubePrimitiveBudget_of_raw_bounds s A B T M hM hB hT).mono
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem affinePrimitiveEnvelope_stride (I : Type*) [Fintype I] (A B T : ℝ≥0) (M V : ℕ)
    {v m : ℕ} (hv : v ≤ V) (hm : m ≤ M) :
    ((v * m : ℕ) : ℝ) ≤ affinePrimitiveEnvelope I A B T M V := by
  have hvm : ((v * m : ℕ) : ℝ) ≤ ((V * M : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul hv hm
  exact hvm.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affineCube_geometric_approximation {B I : Type*}
    [Fintype B] [Nonempty B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} [NeZero K] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M V : ℕ)
    (hM : ∀ b j, (s b j).modulusBound ≤ M) (hW : ∀ b j, (s b j).weightBound ≤ W)
    (hT : ∀ b j, (s b j).weightLipschitz ≤ T) (hv : ∀ b j i, 0 < v b j i)
    (hvV : ∀ b j i, v b j i ≤ V) {C F D E ε : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hupper : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ F * K)
    (hlower : ∀ b, (K : ℝ) ≤ D * ∏ j, ((s b j).length : ℝ))
    (p : ℕ) (hpower : ∀ b j, (K : ℝ) ≤ E * ((s b j).length : ℝ) ^ p)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ Fintype.card B) :
    let U := affinePrimitiveEnvelope I A W T M V
    let Q := affineTorusRadius (Fintype.card I) (n + 1) (Fintype.card B) C F
    let R := affineTorusFactor (Fintype.card I) (n + 1) (Fintype.card B) C F
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) (R * K) J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedCubeIntegerSource s)
            (affineWeightedCubeIntegerSum s u v J center) z : ℝ) : ℂ) -
          integerGridApproximation (weightedCubeIntegerSource s)
            (affineWeightedCubeIntegerSum s u v J center) K (R * K) S z‖ ≤ ε := by
  let U := affinePrimitiveEnvelope I A W T M V
  let Q := affineTorusRadius (Fintype.card I) (n + 1) (Fintype.card B) C F
  let R := affineTorusFactor (Fintype.card I) (n + 1) (Fintype.card B) C F
  have hU : 1 ≤ U := affinePrimitiveEnvelope_one_le I A W T M V
  have h (b) (j) : ScalarCubePrimitiveBudget (s b j) A U :=
    affinePrimitiveEnvelope_vector I (s b j) A W T M V (hM b j) (hW b j) (hT b j)
  have hstride (b) (j) (i) : ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U :=
    affinePrimitiveEnvelope_stride I A W T M V (hvV b j i) ((s b j).modulus_le i |>.trans (hM b j))
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hR : 0 < R := affineTorusFactor_pos _ _ _ _ _
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
  · exact (affine_weightedCube_uniform_spectrum s (fun b j i => (u b j i : ℝ)) v A hA hU hVD hWE
      (Nat.cast_nonneg m) hε h (fun b j => by exact_mod_cast hmin (b, j)) hv hstride
      (R * K) (p * J.card) (Nat.mul_pos hR hK) J hJ hB hsize hscale).2
  · intro k hk
    obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n J.card (p * J.card) hU hWE hε
    obtain ⟨d, hd, hdb, a, ξ, hξ, he⟩ := uniformBlockSpectrumCover_character (Nat.mul_pos hR hK)
      n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hζ hζ1
      (by simpa only [Fintype.card_coe] using hsize) k hk
    obtain ⟨ρ, hρ, hρe⟩ := grid_character_rescale hR k a ξ hξ (by simpa only [Nat.cast_mul] using he)
    refine ⟨d, hd, ?_, a, ρ, ?_, hρe⟩
    · simpa only [Fintype.card_coe] using hdb
    · simpa only [Fintype.card_coe] using hρ
  · exact affine_weightedCube_fundamental_approximation s u v A hA hU hVD hWE (Nat.cast_nonneg m) hε
      h (fun b j => by exact_mod_cast hmin (b, j)) hv hstride (p * J.card) J hJ
      (fun Z => affineWeightedCube_bound_le_torus s u v hC hcoord hupper Z (hJ Z Z.property))
      hB hsize hscale

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affineModerate_geometric_approximation {B I : Type*}
    [Fintype B] [Nonempty B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K : ℕ} [NeZero K] (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ) (stride : B → ℕ)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M V : ℕ)
    (hcM : ∀ b, (c b).modulusBound ≤ M) (hcW : ∀ b, (c b).weightBound ≤ W)
    (hcT : ∀ b, (c b).weightLipschitz ≤ T)
    (hM : ∀ b j, (s b j).modulusBound ≤ M) (hW : ∀ b j, (s b j).weightBound ≤ W)
    (hT : ∀ b j, (s b j).weightLipschitz ≤ T) (hv : ∀ b j i, 0 < v b j i)
    (hvV : ∀ b j i, v b j i ≤ V) (ht : ∀ b, 0 < stride b) (htV : ∀ b, stride b ≤ V)
    {C F D E ε : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hupper : ∀ b, (|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
      (∏ j, ((s b j).length : ℝ)) ≤ F * K)
    (hlower : ∀ b, (K : ℝ) ≤ D * ((c b).length * ∏ j, ((s b j).length : ℝ)))
    (p : ℕ) (hpower : ∀ b j, (K : ℝ) ≤ E * ((s b j).length : ℝ) ^ p)
    (hcpower : ∀ b, (K : ℝ) ≤ E * ((c b).length : ℝ) ^ p)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ Fintype.card B) :
    let U := affinePrimitiveEnvelope I A W T M V
    let Q := affineTorusRadius (Fintype.card I) n (Fintype.card B) C F
    let R := affineTorusFactor (Fintype.card I) n (Fintype.card B) C F
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∑ k, ‖∏ b, affineWeightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) (stride b)
        (fun j i => (u b j i : ℝ)) (v b) (R * K) J k‖) ≤
          uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedModerateIntegerProductSource c s)
            (affineWeightedModerateIntegerSum c s offset stride u v J center) z : ℝ) : ℂ) -
          integerGridApproximation (weightedModerateIntegerProductSource c s)
            (affineWeightedModerateIntegerSum c s offset stride u v J center) K (R * K) S z‖ ≤ ε := by
  let U := affinePrimitiveEnvelope I A W T M V
  let R := affineTorusFactor (Fintype.card I) n (Fintype.card B) C F
  have hU : 1 ≤ U := affinePrimitiveEnvelope_one_le I A W T M V
  have hc (b) : ScalarCubePrimitiveBudget (c b) A U :=
    affinePrimitiveEnvelope_coefficient I (c b) A W T M V (hcM b) (hcW b) (hcT b)
  have h (b) (j) : ScalarCubePrimitiveBudget (s b j) A U :=
    affinePrimitiveEnvelope_vector I (s b j) A W T M V (hM b j) (hW b j) (hT b j)
  have hstride (b) (j) (i) : ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U :=
    affinePrimitiveEnvelope_stride I A W T M V (hvV b j i) ((s b j).modulus_le i |>.trans (hM b j))
  have hcoeff (b) : ((stride b * (c b).modulus none : ℕ) : ℝ) ≤ U :=
    affinePrimitiveEnvelope_stride I A W T M V (htV b) ((c b).modulus_le none |>.trans (hcM b))
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hR : 0 < R := affineTorusFactor_pos _ _ _ _ _
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
      ((((stride b * (c b).modulus none : ℕ) : ℝ) * (c b).length) * ∏ j, ((s b j).length : ℝ)) ≤
        (R : ℝ) * D := by
    have hp : 0 < (((stride b * (c b).modulus none : ℕ) : ℝ) * (c b).length) *
        ∏ j, ((s b j).length : ℝ) := by
      apply mul_pos
      · exact mul_pos (by exact_mod_cast Nat.mul_pos (ht b) ((c b).modulus_pos none))
          (by exact_mod_cast (c b).length_pos)
      · exact Finset.prod_pos (fun j _ => by exact_mod_cast (s b j).length_pos)
    simpa only [Nat.cast_mul] using scaled_grid_volume_bound (Nat.cast_nonneg R) hp
      (affineModerate_physical_volume_lower (c b) (s b) (ht b) hD (hlower b))
  let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
  let S := uniformBlockSpectrumCover J (R * K) n U ((R : ℝ) * D) (m : ℝ) ζ
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · simpa only [S, ζ, Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card
      J (R * K) n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hε hε1
      (by simpa only [Fintype.card_coe] using hsize)
  · exact (affine_weightedModerate_uniform_spectrum c s (fun b => (offset b : ℝ)) stride
      (fun b j i => (u b j i : ℝ)) v A hA hU hVD hWE (Nat.cast_nonneg m) hε hc h
      (fun b => by exact_mod_cast hmin (b, none)) (fun b j => by exact_mod_cast hmin (b, some j))
      ht hv hstride hcoeff (R * K) (p * J.card) (Nat.mul_pos hR hK) J hJ hB hsize hscale).2
  · intro k hk
    obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n J.card (p * J.card) hU hWE hε
    obtain ⟨d, hd, hdb, a, ξ, hξ, he⟩ := uniformBlockSpectrumCover_character (Nat.mul_pos hR hK)
      n (p * J.card) hU hVD hWE (Nat.cast_nonneg m) hζ hζ1
      (by simpa only [Fintype.card_coe] using hsize) k hk
    obtain ⟨ρ, hρ, hρe⟩ := grid_character_rescale hR k a ξ hξ (by simpa only [Nat.cast_mul] using he)
    refine ⟨d, hd, ?_, a, ρ, ?_, hρe⟩
    · simpa only [Fintype.card_coe] using hdb
    · simpa only [Fintype.card_coe] using hρ
  · exact affine_weightedModerate_fundamental_approximation c s offset stride u v A hA hU hVD hWE
      (Nat.cast_nonneg m) hε hc h (fun b => by exact_mod_cast hmin (b, none))
      (fun b j => by exact_mod_cast hmin (b, some j)) ht hv hstride hcoeff (p * J.card) J hJ
      (fun Z => affineWeightedModerate_bound_le_torus c s offset stride u v hC hcoord hupper Z (hJ Z Z.property))
      hB hsize hscale

end Erdos3

end

end OAI
