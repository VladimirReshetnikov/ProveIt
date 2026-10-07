import OAI.Combinatorics.Progressions.Lattices.AffineModerateGeometricApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem cubeRootOffset_relative_bound {I : Type*} {O : ℝ} (hO : 0 ≤ O)
    (c : ℤ) (L : ℕ) (hc : |(c : ℝ)| ≤ O * L) (i : Option I) :
    |(cubeRootOffset c i : ℝ)| + ((1 : ℕ) : ℝ) * L ≤ (O + 1) * L := by
  cases i with
  | none =>
      simp only [cubeRootOffset, Nat.cast_one, one_mul]
      nlinarith
  | some i =>
      simp only [cubeRootOffset, Int.cast_zero, abs_zero, Nat.cast_one, one_mul, zero_add]
      have he := mul_nonneg hO (Nat.cast_nonneg (α := ℝ) L)
      nlinarith

theorem weightedSlice_geometric_approximation {b n q K : ℕ} [NeZero b] [NeZero K]
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M : ℕ)
    (hM : ∀ a j, (s a j).modulusBound ≤ M) (hW : ∀ a j, (s a j).weightBound ≤ W)
    (hT : ∀ a j, (s a j).weightLipschitz ≤ T) {O F D E ε : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    let U := affinePrimitiveEnvelope (Fin q) A W T M 1
    let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
    let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∀ center : J → ℤ, (∑ k, ‖integerGridCoefficient (weightedSliceIntegerSource s root)
          (weightedSliceIntegerSum s root J center) (R * K) k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (weightedSliceIntegerSource s root)
            (weightedSliceIntegerSum s root J center) z : ℝ) : ℂ) -
          integerGridApproximation (weightedSliceIntegerSource s root)
            (weightedSliceIntegerSum s root J center) K (R * K) S z‖ ≤ ε := by
  let u (a : Fin b) (j : Fin (n + 1)) := cubeRootOffset (root a j) (I := Fin q)
  let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  have he := affineCube_geometric_approximation s u (fun _ _ _ => 1) A W T hA M 1 hM hW hT
    (fun _ _ _ => by omega) (fun _ _ _ => le_rfl) (by linarith : 0 ≤ O + 1) hD hE hε hε1
    (fun a j i => cubeRootOffset_relative_bound hO (root a j) (s a j).length (hroot a j) i)
    hupper hlower p hpower J hJ (by simpa only [Fintype.card_fin] using hB)
  dsimp only at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, hchar, ?_⟩
  · intro center
    apply le_trans ?_ hcap
    apply Finset.sum_le_sum
    intro k _
    have heq := weightedSliceIntegerSum_coefficient s root J center (R * K) k
    rw [affineWeightedCubeIntegerSum_coefficient] at heq
    have hn := congrArg norm heq
    simpa only [norm_mul, rectangularGridCharacter_norm, one_mul] using hn.symm.le
  · intro center z hz
    simpa only [u, weightedSliceIntegerSum_mass, weightedSliceIntegerSum_approximation] using happ center z hz

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem moderateSlice_geometric_approximation {b n q K : ℕ} [NeZero b] [NeZero K]
    (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin n → NormalizedScalarCubeSource (Fin q))
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (root : Fin b → Fin n → ℤ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M V : ℕ) (hV : 1 ≤ V)
    (hcM : ∀ a, (c a).modulusBound ≤ M) (hcW : ∀ a, (c a).weightBound ≤ W)
    (hcT : ∀ a, (c a).weightLipschitz ≤ T)
    (hM : ∀ a j, (s a j).modulusBound ≤ M) (hW : ∀ a j, (s a j).weightBound ≤ W)
    (hT : ∀ a j, (s a j).weightLipschitz ≤ T) (ht : ∀ a, 0 < stride a) (htV : ∀ a, stride a ≤ V)
    {O F D E ε : ℝ} (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (|(offset a : ℝ)| + (stride a : ℝ) * (c a).length) *
      (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ((c a).length * ∏ j, ((s a j).length : ℝ)))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (hcpower : ∀ a, (K : ℝ) ≤ E * ((c a).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) :
    let U := affinePrimitiveEnvelope (Fin q) A W T M V
    let Q := affineTorusRadius (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
    let R := affineTorusFactor (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
    let ζ := uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
    ∃ S : Finset (J → Fin (R * K)),
      (S.card : ℝ) ≤ uniformSpectrumSizeConstant n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) /
          ε ^ max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)) ∧
      (∀ center : J → ℤ, (∑ k, ‖integerGridCoefficient (moderateSliceIntegerSource c s root)
          (moderateSliceIntegerSum c s offset stride root J center) (R * K) k‖) ≤
        uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound n J.card (p * J.card)
        U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ζ ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ),
          (∀ Z, |ξ Z| ≤ 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) / ζ ^ majorArcCoverExponent n J.card) ∧
          ∀ Z, ((k Z).val : ℝ) / (R * K) = (a Z : ℝ) / d + ξ Z / K) ∧
      ∀ center z : J → ℤ, centeredFundamentalBox Q K center z →
        ‖(((K : ℝ) ^ J.card * finiteImageMass (moderateSliceIntegerSource c s root)
            (moderateSliceIntegerSum c s offset stride root J center) z : ℝ) : ℂ) -
          integerGridApproximation (moderateSliceIntegerSource c s root)
            (moderateSliceIntegerSum c s offset stride root J center) K (R * K) S z‖ ≤ ε := by
  let u (a : Fin b) (j : Fin n) := cubeRootOffset (root a j) (I := Fin q)
  let R := affineTorusFactor (Fintype.card (Fin q)) n (Fintype.card (Fin b)) (O + 1) F
  have he := affineModerate_geometric_approximation c s offset stride u (fun _ _ _ => 1) A W T hA M V
    hcM hcW hcT hM hW hT (fun _ _ _ => by omega) (fun _ _ _ => hV) ht htV
    (by linarith : 0 ≤ O + 1) hD hE hε hε1
    (fun a j i => cubeRootOffset_relative_bound hO (root a j) (s a j).length (hroot a j) i)
    hupper hlower p hpower hcpower J hJ (by simpa only [Fintype.card_fin] using hB)
  dsimp only at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, hchar, ?_⟩
  · intro center
    apply le_trans ?_ hcap
    apply Finset.sum_le_sum
    intro k _
    have heq := moderateSliceIntegerSum_coefficient c s offset stride root J center (R * K) k
    rw [affineWeightedModerateIntegerSum_coefficient] at heq
    have hn := congrArg norm heq
    simpa only [norm_mul, rectangularGridCharacter_norm, one_mul] using hn.symm.le
  · intro center z hz
    simpa only [u, moderateSliceIntegerSum_mass, moderateSliceIntegerSum_approximation] using happ center z hz

end Erdos3

end

end OAI
