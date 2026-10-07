import GowersSzemeredi.Proofs13SingletonRecurrence
import GowersSzemeredi.Proofs13UntrimmedRecurrence

/-! Precise coverage of the remaining Lemma 13.5 scales. The singleton
and polynomial branches overlap whenever there are at least 311 frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private theorem twice_square_tower_le (a : Nat) :
    2 * ((2 : Nat) ^ (2 ^ a)) ^ 2 ≤ 2 ^ (2 ^ (a + 2)) := by
  rw [← pow_mul, ← pow_succ']
  apply Nat.pow_le_pow_right (n := 2) (by norm_num)
  rw [pow_add]
  norm_num only [Nat.reducePow]
  have h : 1 ≤ (2 : Nat) ^ a := one_le_pow₀ (by norm_num)
  omega

theorem polynomial_threshold_twice_le_tower (d : Nat) :
    2 * polynomialPartitionThreshold d ≤ 2 ^ (2 ^ (40 * d ^ 3 + 2)) := by
  unfold polynomialPartitionThreshold weylThreshold
  exact twice_square_tower_le _

private theorem tower_power_identity (a b c : Nat) :
    ((2 : Nat) ^ (2 ^ a)) ^ ((2 ^ b) ^ c) = 2 ^ (2 ^ (a + b * c)) := by
  rw [← pow_mul, ← pow_mul, ← pow_add]

theorem simultaneous_partition_threshold_le_tower (k q b : Nat)
    (hK : polynomialPartitionConstant k ≤ 2 ^ b) :
    simultaneousPolynomialThreshold k q ≤ 2 ^ (2 ^ (40 * k ^ 3 + 2 + b * (q - 1))) := by
  calc
    simultaneousPolynomialThreshold k q =
      (2 * polynomialPartitionThreshold k) ^ (polynomialPartitionConstant k ^ (q - 1)) := rfl
    _ ≤ (2 ^ (2 ^ (40 * k ^ 3 + 2))) ^ (polynomialPartitionConstant k ^ (q - 1)) :=
      Nat.pow_le_pow_left (polynomial_threshold_twice_le_tower k) _
    _ ≤ (2 ^ (2 ^ (40 * k ^ 3 + 2))) ^ ((2 ^ b) ^ (q - 1)) :=
      Nat.pow_le_pow_right (n := 2 ^ (2 ^ (40 * k ^ 3 + 2)))
        (one_le_pow₀ (by norm_num : (1 : Nat) ≤ 2)) (Nat.pow_le_pow_left hK _)
    _ = _ := tower_power_identity _ _ _

theorem quadratic_partition_threshold_le_singleton_cutoff {q : Nat} (hq : 311 ≤ q) :
    simultaneousPolynomialThreshold 2 q ≤ 2 ^ (2 ^ (12 * q)) := by
  have hK : polynomialPartitionConstant 2 ≤ 2 ^ 11 := by norm_num [polynomialPartitionConstant]
  have hb := simultaneous_partition_threshold_le_tower 2 q 11 hK
  apply hb.trans
  apply Nat.pow_le_pow_right (n := 2) (by norm_num)
  apply Nat.pow_le_pow_right (n := 2) (by norm_num)
  omega

theorem stage134_odd_of_polynomial_threshold {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hthreshold : simultaneousPolynomialThreshold 2 D.q < D.P.length) : N != 2 := by
  have hL : 16 < D.P.length :=
    ((section5PolynomialPartitionThreshold_ge_sixteen (by norm_num : 1 ≤ 2)).trans
      (polynomialPartitionThreshold_le_simultaneousPolynomialThreshold 2 D.q)).trans_lt hthreshold
  have hLN : D.P.length ≤ N := by
    rw [← h134.2.2.1]
    simpa only [ZMod.card] using Finset.card_le_univ D.P.carrier
  have hN : 16 < N := hL.trans_le hLN
  apply bne_iff_ne.mpr
  intro heq
  rw [heq] at hN
  norm_num at hN

theorem lemma_13_5_large_frequency_family {N : Nat} [NeZero N]
    (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hq : 311 ≤ D.q) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  by_cases hsmall : D.P.length ≤ 2 ^ (2 ^ (12 * D.q))
  · exact lemma_13_5_printed_small_case S D theta h134 hsmall
  · have hthreshold : simultaneousPolynomialThreshold 2 D.q < D.P.length :=
      (quadratic_partition_threshold_le_singleton_cutoff hq).trans_lt (lt_of_not_ge hsmall)
    obtain ⟨E, hE, _⟩ := lemma_13_5_from_polynomial_threshold hprime
      (stage134_odd_of_polynomial_threshold S D theta h134 hthreshold) S D theta h134 hthreshold
    exact ⟨E, hE⟩

theorem lemma_13_5_failure_forces_intermediate_scale {N : Nat} [NeZero N]
    (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hfail : ¬ ∃ E : Stage135Data N, IsStage135Data S D E) :
    D.q < 311 ∧ 2 ^ (2 ^ (12 * D.q)) < D.P.length ∧
      D.P.length ≤ simultaneousPolynomialThreshold 2 D.q := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hq
    exact hfail (lemma_13_5_large_frequency_family hprime S D theta h134 (le_of_not_gt hq))
  · by_contra hsmall
    exact hfail (lemma_13_5_printed_small_case S D theta h134 (le_of_not_gt hsmall))
  · by_contra hlarge
    obtain ⟨E, hE, _⟩ := lemma_13_5_from_polynomial_threshold hprime
      (stage134_odd_of_polynomial_threshold S D theta h134 (lt_of_not_ge hlarge))
      S D theta h134 (lt_of_not_ge hlarge)
    exact hfail ⟨E, hE⟩

end LeanProofs.GowersSzemeredi
