import GRHArticle.ProgressionFree.PolynomialIrreducibleDegrees

/-!
# Lower bounds for monic irreducibles in a finite field

The proper divisors of `d` are at most `d / 2`. Subtracting their contributions
to the Frobenius degree gives the irreducible count used in `gpp:thm:largeq`.
The resulting half bound holds even over the field with two elements.
-/

namespace GRHArticle.ProgressionFree

variable (F : Type*) [Field F] [Fintype F]

theorem polynomialIrreducibleCount_one : polynomialIrreducibleCount F 1 = Fintype.card F := by
  simpa using sum_divisors_mul_polynomialIrreducibleCount (F := F) 1 (by decide)

/-- The finite geometric tail accounts for all contributions from proper
subfields of the degree-`d` extension. -/
theorem pow_card_le_degree_mul_irreducibleCount_add (d : ℕ) (hd : 0 < d) :
    Fintype.card F ^ d ≤ d * polynomialIrreducibleCount F d +
      ∑ i ∈ Finset.range (d / 2), Fintype.card F ^ (i+1) := by
  have hsub : d.properDivisors ⊆ Finset.Ico 1 (d / 2 + 1) := by
    intro i hi
    obtain ⟨⟨k, hk⟩, hlt⟩ := Nat.mem_properDivisors.mp hi
    have hip : 0 < i := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hk; omega
    have hk₂ : 2 ≤ k := by
      by_contra! h
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · simp at hk; omega
      · simp at hk; omega
    have hm := Nat.mul_le_mul_left i hk₂
    exact Finset.mem_Ico.mpr ⟨hip, by omega⟩
  rw [← sum_divisors_mul_polynomialIrreducibleCount (F := F) d hd,
    ← Nat.insert_self_properDivisors hd.ne', Finset.sum_insert Nat.self_notMem_properDivisors]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ i ∈ d.properDivisors, Fintype.card F ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact degree_mul_polynomialIrreducibleCount_le i (Finset.mem_Ico.mp (hsub hi)).1
    _ ≤ ∑ i ∈ Finset.Ico 1 (d/2+1), Fintype.card F ^ i := Finset.sum_le_sum_of_subset hsub
    _ = _ := by simp [Finset.sum_Ico_eq_sum_range, Nat.add_comm]

private theorem geometric_prefix_le_next_power (q n : ℕ) (hq : 2 ≤ q) :
    ∑ i ∈ Finset.range n, q ^ (i+1) ≤ q ^ (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ q (n+1)]
    calc
      _ ≤ q^(n+1) * 2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hq

/-- In *every* finite field, elements of full degree make up at least
half of each extension, including the quadratic extension of the binary field. -/
theorem pow_card_le_twice_degree_mul_polynomialIrreducibleCount (d : ℕ) (hd : 0 < d) :
    Fintype.card F ^ d ≤ 2 * (d * polynomialIrreducibleCount F d) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have h := pow_card_le_degree_mul_irreducibleCount_add F d hd
  change q^d ≤ d * polynomialIrreducibleCount F d + ∑ i ∈ Finset.range (d/2), q^(i+1) at h
  change q^d ≤ _
  suffices ht : 2*(∑ i ∈ Finset.range (d/2), q^(i+1)) ≤ q^d by omega
  by_cases hd₂ : d ≤ 2
  · obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    · simp
    · simpa [pow_two] using Nat.mul_le_mul_right q hq
  · calc
      _ ≤ 2 * q^(d/2+1) := Nat.mul_le_mul_left _ (geometric_prefix_le_next_power _ _ hq)
      _ ≤ q^(d/2+1+1) := by rw [pow_succ q (d/2+1), mul_comm]; exact Nat.mul_le_mul_left _ hq
      _ ≤ q^d := Nat.pow_le_pow_right (by omega) (by omega)

end GRHArticle.ProgressionFree
