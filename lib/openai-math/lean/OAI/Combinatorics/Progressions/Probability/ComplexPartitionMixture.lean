import OAI.Combinatorics.Progressions.Sampling.FrozenPartitionScore

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_partitionCell_complex {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (∑ k, ∑ x ∈ partitionCell cell k, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem complex_expect_partition_mixture {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k, ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  classical
  have hcell (k : K) : ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) =
      (∑ x ∈ partitionCell cell k, f x) / Fintype.card X := by
    rw [Finset.expect_eq_sum_div_card]
    by_cases hc : (partitionCell cell k).card = 0
    · have hempty := Finset.card_eq_zero.mp hc
      simp only [hempty, Finset.card_empty, Nat.cast_zero, Finset.sum_empty, zero_div, mul_zero]
    · have hc' : ((partitionCell cell k).card : ℂ) ≠ 0 := by exact_mod_cast hc
      calc
        _ = (((partitionCell cell k).card : ℂ) / (partitionCell cell k).card) *
            ((∑ x ∈ partitionCell cell k, f x) / Fintype.card X) := by ring
        _ = _ := by rw [div_self hc', one_mul]
  simp_rw [hcell]
  rw [← Finset.sum_div, sum_partitionCell_complex, Fintype.expect_eq_sum_div_card]

theorem complex_expect_partition_count_weights {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k,
      (((partitionCell cell k).card : ℝ) / (∑ j, ((partitionCell cell j).card : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  rw [card_partitionCell_sum]
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using complex_expect_partition_mixture cell f

end Erdos3

end

end OAI
