import OAI.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedPrime_small_support (Q degree m : ℕ) (hm : 0 < m) (hmQ : m ≤ Q) (hQdegree : Q ≤ 2 ^ degree) :
    ∃ S : Finset (BoundedPrime Q), S.card ≤ degree ∧ m ∣ ∏ j ∈ S, boundedPrimePower Q j := by
  refine ⟨periodPrimeCoordinates (boundedPrime Q) m, ?_, ?_⟩
  · exact periodPrimeCoordinates_card_le_of_le_pow (boundedPrime Q) (boundedPrime_prime Q)
      (boundedPrime_injective Q) hm (hmQ.trans hQdegree)
  · exact periodPrimeCoordinates_modulus_dvd_product (boundedPrime Q) (boundedPrimeExponent Q)
      (boundedPrime_prime Q) m (boundedPrimeProduct_captures hm hmQ)

theorem bounded_prime_physical_residual_correlation {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample u z.val))| ≤
      ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
        ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap (BoundedPrime Q) degree eta) ^ 2 +
          (fullSmoothPairError (Fintype.card I) k Q C κ δ +
            (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
              (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2)) := by
  obtain ⟨S, hS, hm⟩ := boundedPrime_small_support Q degree (affinePairModulus t u)
    (affinePairModulus_pos t u k hne) hQ hQdegree
  exact normalized_physical_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ
    hmesh hsmall origin hZ lo N hside (boundedPrimePower Q) (boundedPrimePower_pairwise Q) degree f g hf hg
    eta ρ modLog dimLog accLog hρ heta hmodLog hacc
    (fun j => (Nat.cast_le.mpr (boundedPrimePower_le Q j)).trans hQlog) hdim hlarge hwhole hlength S hS hm

end Erdos3

end

end OAI
