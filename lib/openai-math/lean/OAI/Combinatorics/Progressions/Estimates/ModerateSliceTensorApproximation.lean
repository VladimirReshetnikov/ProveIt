/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.ModerateSliceGeometricApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointRetainedExpansion_card_le_product {D : Type*} [Fintype D] [DecidableEq D]
    {A : D → Type*} (S : ∀ d, Finset (A d)) (B : D → ℝ)
    (hB : ∀ d, ((S d).card : ℝ) ≤ B d) :
    (Fintype.card (∀ d, S d) : ℝ) ≤ ∏ d, B d := by
  rw [jointRetainedExpansion_count, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun d _ => hB d)

theorem independentPeriodTensor_coefficient_mass {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (K M : D → ℕ) [∀ d, NeZero (M d)] (S : ∀ d, Finset (J d → Fin (M d)))
    {C : ℝ} (hKM : ∀ d, K d ≤ M d)
    (hcap : ∀ d, (∑ k, ‖integerGridCoefficient (p d) (Y d) (M d) k‖) ≤ C) :
    (∑ a : ∀ d, S d, ‖∏ d, integerRetainedCoefficient (p d) (Y d) (K d) (M d) (a d)‖) ≤
      C ^ Fintype.card D := by
  apply jointRetainedExpansion_mass_bound
  intro d
  exact integerRetainedCoefficient_mass_le (p d) (Y d) (K d) (M d) (S d) (hKM d) (hcap d)

theorem independentPeriodTensor_approximation {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (K M : D → ℕ) [∀ d, NeZero (M d)] (S : ∀ d, Finset (J d → Fin (M d)))
    (z : ∀ d, J d → ℤ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hKM : ∀ d, K d ≤ M d)
    (hcap : ∀ d, (∑ k, ‖integerGridCoefficient (p d) (Y d) (M d) k‖) ≤ C)
    (herr : ∀ d, ‖(((K d : ℝ) ^ Fintype.card (J d) *
        finiteImageMass (p d) (Y d) (z d) : ℝ) : ℂ) -
      integerGridApproximation (p d) (Y d) (K d) (M d) (S d) (z d)‖ ≤
        jointGridAxisTolerance (Fintype.card D) (C + 1) ε) :
    ‖(((∏ d, (K d : ℝ) ^ Fintype.card (J d)) *
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z : ℝ) : ℂ) -
        jointRetainedExpansion S (fun d => integerRetainedCoefficient (p d) (Y d) (K d) (M d))
          (fun d k w => star (rectangularGridCharacter (M d) k w)) z‖ ≤ ε := by
  have hC1 : 1 ≤ C + 1 := by linarith
  have hs := jointGridAxisTolerance_spec (Fintype.card D) (by linarith : 0 ≤ C + 1) hε
  have happ (d) := integerGridApproximation_norm_le (p d) (Y d) (K d) (M d) (S d)
    (z d) (hKM d) (hcap d)
  have hexact (d) : ‖(((K d : ℝ) ^ Fintype.card (J d) *
      finiteImageMass (p d) (Y d) (z d) : ℝ) : ℂ)‖ ≤ C + 1 := by
    let f := integerGridApproximation (p d) (Y d) (K d) (M d) (S d) (z d)
    let a : ℂ := ((K d : ℝ) ^ Fintype.card (J d) * finiteImageMass (p d) (Y d) (z d) : ℝ)
    change ‖a‖ ≤ C + 1
    calc
      ‖a‖ = ‖(a - f) + f‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - f‖ + ‖f‖ := norm_add_le _ _
      _ ≤ jointGridAxisTolerance (Fintype.card D) (C + 1) ε + C := add_le_add (herr d) (happ d)
      _ ≤ C + 1 := by linarith [hs.2.1]
  rw [jointRetainedExpansion_eq_product]
  simp_rw [← integerGridApproximation_eq_sum]
  exact (scaledImageMass_pi_approximation p Y z (fun d => (K d : ℝ) ^ Fintype.card (J d))
    (fun d => integerGridApproximation (p d) (Y d) (K d) (M d) (S d) (z d))
    hC1 hs.1.le hexact (fun d => (happ d).trans (by linarith)) herr).trans hs.2.2

noncomputable def finiteFamilyCap {D : Type*} [Fintype D] (C : D → ℝ) : ℝ :=
  ∑ d, max 0 (C d)

theorem finiteFamilyCap_nonneg {D : Type*} [Fintype D] (C : D → ℝ) : 0 ≤ finiteFamilyCap C :=
  Finset.sum_nonneg (fun _d _ => le_max_left _ _)

theorem le_finiteFamilyCap {D : Type*} [Fintype D] (C : D → ℝ) (d : D) : C d ≤ finiteFamilyCap C := by
  classical
  exact (le_max_right _ _).trans (Finset.single_le_sum (fun e _ => le_max_left 0 (C e)) (Finset.mem_univ d))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedSliceTensor_approximation {D : Type*} [Fintype D] [DecidableEq D]
    (b n q K : D → ℕ) [∀ d, NeZero (b d)] [∀ d, NeZero (K d)]
    (s : ∀ d, Fin (b d) → Fin (n d + 1) → NormalizedScalarCubeSource (Fin (q d)))
    (root : ∀ d, Fin (b d) → Fin (n d + 1) → ℤ)
    (A W T : D → ℝ≥0) (hA : ∀ d, LipschitzWith (A d) Real.smoothTransition) (M : D → ℕ)
    (hM : ∀ d a j, (s d a j).modulusBound ≤ M d)
    (hW : ∀ d a j, (s d a j).weightBound ≤ W d)
    (hT : ∀ d a j, (s d a j).weightLipschitz ≤ T d) (O F V E : D → ℝ)
    (hO : ∀ d, 0 ≤ O d) (hV : ∀ d, 0 ≤ V d) (hE : ∀ d, 0 ≤ E d)
    (hroot : ∀ d a j, |(root d a j : ℝ)| ≤ O d * (s d a j).length)
    (hupper : ∀ d a, (∏ j, ((s d a j).length : ℝ)) ≤ F d * K d)
    (hlower : ∀ d a, (K d : ℝ) ≤ V d * ∏ j, ((s d a j).length : ℝ))
    (p : D → ℕ) (hpower : ∀ d a j, (K d : ℝ) ≤ E d * ((s d a j).length : ℝ) ^ p d)
    (J : ∀ d, Finset (Finset (Fin (q d)))) (hJ : ∀ d S, S ∈ J d → S.card ≤ n d + 1)
    (hB : ∀ d, uniformSpectrumBlockCount (n d) (J d).card (p d * (J d).card) ≤ b d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let U := fun d => affinePrimitiveEnvelope (Fin (q d)) (A d) (W d) (T d) (M d) 1
    let Q := fun d => affineTorusRadius (Fintype.card (Fin (q d))) (n d + 1)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    let R := fun d => affineTorusFactor (Fintype.card (Fin (q d))) (n d + 1)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    let C := finiteFamilyCap (fun d => uniformSpectrumAbsoluteCap (n d) (J d).card
      (p d * (J d).card) (U d) ((R d : ℝ) * V d) (((R d : ℝ) * E d) ^ (J d).card))
    let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
    let ζ := fun d => uniformBlockRetainedBias (n d) (J d).card (p d * (J d).card)
      (U d) ((R d : ℝ) * V d) (((R d : ℝ) * E d) ^ (J d).card) δ
    ∃ S : ∀ d, Finset (J d → Fin (R d * K d)),
      (Fintype.card (∀ d, S d) : ℝ) ≤ ∏ d,
        uniformSpectrumSizeConstant (n d) (J d).card (p d * (J d).card)
          (U d) ((R d : ℝ) * V d) (((R d : ℝ) * E d) ^ (J d).card) /
            δ ^ max (majorArcSpectrumExponent (n d) (J d).card)
              (majorArcLengthExponent (n d) * (p d * (J d).card)) ∧
      (∀ center : ∀ d, J d → ℤ,
        (∑ a : ∀ d, S d, ‖∏ d, integerRetainedCoefficient
          (weightedSliceIntegerSource (s d) (root d))
          (weightedSliceIntegerSum (s d) (root d) (J d) (center d)) (K d) (R d * K d) (a d)‖) ≤
          C ^ Fintype.card D) ∧
      (∀ d k, k ∈ S d → ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ uniformCharacterDenominatorBound
        (n d) (J d).card (p d * (J d).card) (U d) ((R d : ℝ) * V d)
          (((R d : ℝ) * E d) ^ (J d).card) (ζ d) ∧
        ∃ (a : J d → ℤ) (ξ : J d → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant (n d) (J d).card (U d) ((R d : ℝ) * V d) /
            (ζ d) ^ majorArcCoverExponent (n d) (J d).card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R d * K d) = (a Z : ℝ) / m + ξ Z / K d) ∧
      ∀ center z : ∀ d, J d → ℤ,
        (∀ d, centeredFundamentalBox (Q d) (K d) (center d) (z d)) →
        ‖(((∏ d, (K d : ℝ) ^ (J d).card) *
          finiteImageMass (FiniteProbabilityWeights.pi (fun d => weightedSliceIntegerSource (s d) (root d)))
            (fun x d => weightedSliceIntegerSum (s d) (root d) (J d) (center d) (x d)) z : ℝ) : ℂ) -
          jointRetainedExpansion S
            (fun d => integerRetainedCoefficient (weightedSliceIntegerSource (s d) (root d))
              (weightedSliceIntegerSum (s d) (root d) (J d) (center d)) (K d) (R d * K d))
            (fun d k w => star (rectangularGridCharacter (R d * K d) k w)) z‖ ≤ ε := by
  dsimp only
  let U := fun d => affinePrimitiveEnvelope (Fin (q d)) (A d) (W d) (T d) (M d) 1
  let R := fun d => affineTorusFactor (Fintype.card (Fin (q d))) (n d + 1)
    (Fintype.card (Fin (b d))) (O d + 1) (F d)
  let cap := fun d => uniformSpectrumAbsoluteCap (n d) (J d).card (p d * (J d).card)
    (U d) ((R d : ℝ) * V d) (((R d : ℝ) * E d) ^ (J d).card)
  let C := finiteFamilyCap cap
  let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
  have hC : 0 ≤ C := finiteFamilyCap_nonneg cap
  have hδ := jointGridAxisTolerance_spec (Fintype.card D) (by linarith : 0 ≤ C + 1) hε
  have hi (d : D) := weightedSlice_geometric_approximation (s d) (root d) (A d) (W d) (T d)
    (hA d) (M d) (hM d) (hW d) (hT d) (hO d) (hV d) (hE d) hδ.1 (hδ.2.1.trans hε1)
    (hroot d) (hupper d) (hlower d) (p d) (hpower d) (J d) (hJ d) (hB d)
  dsimp only at hi
  choose S hcard hcap hchar happ using hi
  have hKM (d : D) : K d ≤ R d * K d := by
    have hR := affineTorusFactor_pos (Fintype.card (Fin (q d))) (n d + 1)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    exact Nat.le_mul_of_pos_left (K d) hR
  have hcapC (center : ∀ d, J d → ℤ) (d : D) :
      (∑ k, ‖integerGridCoefficient (weightedSliceIntegerSource (s d) (root d))
        (weightedSliceIntegerSum (s d) (root d) (J d) (center d)) (R d * K d) k‖) ≤ C :=
    (hcap d (center d)).trans (le_finiteFamilyCap cap d)
  refine ⟨S, jointRetainedExpansion_card_le_product S _ hcard, ?_, hchar, ?_⟩
  · intro center
    exact independentPeriodTensor_coefficient_mass
      (fun d => weightedSliceIntegerSource (s d) (root d))
      (fun d => weightedSliceIntegerSum (s d) (root d) (J d) (center d))
      K (fun d => R d * K d) S hKM (hcapC center)
  · intro center z hz
    simpa only [Fintype.card_coe] using independentPeriodTensor_approximation
      (fun d => weightedSliceIntegerSource (s d) (root d))
      (fun d => weightedSliceIntegerSum (s d) (root d) (J d) (center d))
      K (fun d => R d * K d) S z hC hε hε1 hKM (hcapC center)
      (fun d => by simpa only [Fintype.card_coe] using happ d (center d) (z d) (hz d))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem moderateSliceTensor_approximation {D : Type*} [Fintype D] [DecidableEq D]
    (b n q K : D → ℕ) [∀ d, NeZero (b d)] [∀ d, NeZero (K d)]
    (c : ∀ d, Fin (b d) → NormalizedScalarCubeSource Empty)
    (s : ∀ d, Fin (b d) → Fin (n d) → NormalizedScalarCubeSource (Fin (q d)))
    (offset : ∀ d, Fin (b d) → ℤ) (stride : ∀ d, Fin (b d) → ℕ)
    (root : ∀ d, Fin (b d) → Fin (n d) → ℤ)
    (A W T : D → ℝ≥0) (hA : ∀ d, LipschitzWith (A d) Real.smoothTransition) (M V : D → ℕ) (hV : ∀ d, 1 ≤ V d)
    (hcM : ∀ d a, (c d a).modulusBound ≤ M d)
    (hcW : ∀ d a, (c d a).weightBound ≤ W d)
    (hcT : ∀ d a, (c d a).weightLipschitz ≤ T d)
    (hM : ∀ d a j, (s d a j).modulusBound ≤ M d)
    (hW : ∀ d a j, (s d a j).weightBound ≤ W d)
    (hT : ∀ d a j, (s d a j).weightLipschitz ≤ T d)
    (ht : ∀ d a, 0 < stride d a) (htV : ∀ d a, stride d a ≤ V d) (O F H E : D → ℝ)
    (hO : ∀ d, 0 ≤ O d) (hH : ∀ d, 0 ≤ H d) (hE : ∀ d, 0 ≤ E d)
    (hroot : ∀ d a j, |(root d a j : ℝ)| ≤ O d * (s d a j).length)
    (hupper : ∀ d a, (|(offset d a : ℝ)| + (stride d a : ℝ) * (c d a).length) *
      (∏ j, ((s d a j).length : ℝ)) ≤ F d * K d)
    (hlower : ∀ d a, (K d : ℝ) ≤ H d * ((c d a).length * ∏ j, ((s d a j).length : ℝ)))
    (p : D → ℕ) (hpower : ∀ d a j, (K d : ℝ) ≤ E d * ((s d a j).length : ℝ) ^ p d)
    (hcpower : ∀ d a, (K d : ℝ) ≤ E d * ((c d a).length : ℝ) ^ p d)
    (J : ∀ d, Finset (Finset (Fin (q d)))) (hJ : ∀ d S, S ∈ J d → S.card ≤ n d)
    (hB : ∀ d, uniformSpectrumBlockCount (n d) (J d).card (p d * (J d).card) ≤ b d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let U := fun d => affinePrimitiveEnvelope (Fin (q d)) (A d) (W d) (T d) (M d) (V d)
    let Q := fun d => affineTorusRadius (Fintype.card (Fin (q d))) (n d)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    let R := fun d => affineTorusFactor (Fintype.card (Fin (q d))) (n d)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    let C := finiteFamilyCap (fun d => uniformSpectrumAbsoluteCap (n d) (J d).card
      (p d * (J d).card) (U d) ((R d : ℝ) * H d) (((R d : ℝ) * E d) ^ (J d).card))
    let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
    let ζ := fun d => uniformBlockRetainedBias (n d) (J d).card (p d * (J d).card)
      (U d) ((R d : ℝ) * H d) (((R d : ℝ) * E d) ^ (J d).card) δ
    ∃ S : ∀ d, Finset (J d → Fin (R d * K d)),
      (Fintype.card (∀ d, S d) : ℝ) ≤ ∏ d,
        uniformSpectrumSizeConstant (n d) (J d).card (p d * (J d).card)
          (U d) ((R d : ℝ) * H d) (((R d : ℝ) * E d) ^ (J d).card) /
            δ ^ max (majorArcSpectrumExponent (n d) (J d).card)
              (majorArcLengthExponent (n d) * (p d * (J d).card)) ∧
      (∀ center : ∀ d, J d → ℤ,
        (∑ a : ∀ d, S d, ‖∏ d, integerRetainedCoefficient
          (moderateSliceIntegerSource (c d) (s d) (root d))
          (moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d)) (K d) (R d * K d) (a d)‖) ≤
          C ^ Fintype.card D) ∧
      (∀ d k, k ∈ S d → ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ uniformCharacterDenominatorBound
        (n d) (J d).card (p d * (J d).card) (U d) ((R d : ℝ) * H d)
          (((R d : ℝ) * E d) ^ (J d).card) (ζ d) ∧
        ∃ (a : J d → ℤ) (ξ : J d → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant (n d) (J d).card (U d) ((R d : ℝ) * H d) /
            (ζ d) ^ majorArcCoverExponent (n d) (J d).card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R d * K d) = (a Z : ℝ) / m + ξ Z / K d) ∧
      ∀ center z : ∀ d, J d → ℤ,
        (∀ d, centeredFundamentalBox (Q d) (K d) (center d) (z d)) →
        ‖(((∏ d, (K d : ℝ) ^ (J d).card) *
          finiteImageMass (FiniteProbabilityWeights.pi (fun d => moderateSliceIntegerSource (c d) (s d) (root d)))
            (fun x d => moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d) (x d)) z : ℝ) : ℂ) -
          jointRetainedExpansion S
            (fun d => integerRetainedCoefficient (moderateSliceIntegerSource (c d) (s d) (root d))
              (moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d)) (K d) (R d * K d))
            (fun d k w => star (rectangularGridCharacter (R d * K d) k w)) z‖ ≤ ε := by
  dsimp only
  let U := fun d => affinePrimitiveEnvelope (Fin (q d)) (A d) (W d) (T d) (M d) (V d)
  let R := fun d => affineTorusFactor (Fintype.card (Fin (q d))) (n d)
    (Fintype.card (Fin (b d))) (O d + 1) (F d)
  let cap := fun d => uniformSpectrumAbsoluteCap (n d) (J d).card (p d * (J d).card)
    (U d) ((R d : ℝ) * H d) (((R d : ℝ) * E d) ^ (J d).card)
  let C := finiteFamilyCap cap
  let δ := jointGridAxisTolerance (Fintype.card D) (C + 1) ε
  have hC : 0 ≤ C := finiteFamilyCap_nonneg cap
  have hδ := jointGridAxisTolerance_spec (Fintype.card D) (by linarith : 0 ≤ C + 1) hε
  have hi (d : D) := moderateSlice_geometric_approximation (c d) (s d) (offset d) (stride d)
    (root d) (A d) (W d) (T d) (hA d) (M d) (V d) (hV d) (hcM d) (hcW d) (hcT d)
    (hM d) (hW d) (hT d) (ht d) (htV d) (hO d) (hH d) (hE d) hδ.1 (hδ.2.1.trans hε1)
    (hroot d) (hupper d) (hlower d) (p d) (hpower d) (hcpower d) (J d) (hJ d) (hB d)
  dsimp only at hi
  choose S hcard hcap hchar happ using hi
  have hKM (d : D) : K d ≤ R d * K d := by
    have hR := affineTorusFactor_pos (Fintype.card (Fin (q d))) (n d)
      (Fintype.card (Fin (b d))) (O d + 1) (F d)
    exact Nat.le_mul_of_pos_left (K d) hR
  have hcapC (center : ∀ d, J d → ℤ) (d : D) :
      (∑ k, ‖integerGridCoefficient (moderateSliceIntegerSource (c d) (s d) (root d))
        (moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d)) (R d * K d) k‖) ≤ C :=
    (hcap d (center d)).trans (le_finiteFamilyCap cap d)
  refine ⟨S, jointRetainedExpansion_card_le_product S _ hcard, ?_, hchar, ?_⟩
  · intro center
    exact independentPeriodTensor_coefficient_mass
      (fun d => moderateSliceIntegerSource (c d) (s d) (root d))
      (fun d => moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d))
      K (fun d => R d * K d) S hKM (hcapC center)
  · intro center z hz
    simpa only [Fintype.card_coe] using independentPeriodTensor_approximation
      (fun d => moderateSliceIntegerSource (c d) (s d) (root d))
      (fun d => moderateSliceIntegerSum (c d) (s d) (offset d) (stride d) (root d) (J d) (center d))
      K (fun d => R d * K d) S z hC hε hε1 hKM (hcapC center)
      (fun d => by simpa only [Fintype.card_coe] using happ d (center d) (z d) (hz d))

end Erdos3

end

end OAI
