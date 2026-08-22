import ExponentialIdentities.TwoBaseIntegerExponent.AllLayerUnitBasis

/-!
# Finite aggregate bounds for unit-ordering gains

`AllLayerUnitBasis` supplies complete-determinant divisors with dyadic weights
`j + v₂(j!)` and triadic weights `⌊j/2⌋ + v₃(⌊j/2⌋!)`.  This file packages their exact
one-block sums and proves uniform quadratic and cubic bounds.  In particular, at most `S`
blocks, each of size at most `S`, have total dyadic gain at most `S ^ 3`; twice the total
triadic gain has the same bound.

These are finite combinatorial estimates.  Applying them to the mixed determinant still
requires identifying its concrete vertical and horizontal unit-Vandermonde blocks and proving
the corresponding block-cardinality bounds.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset

/-- Total strengthened dyadic-unit weight in a univariate block of size `s`. -/
def twoUnitBlockGain (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, twoUnitOrderingWeight j

/-- Total strengthened triadic-unit weight in a univariate block of size `s`. -/
def threeUnitBlockGain (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, threeUnitOrderingWeight j

/-- Legendre's digit-sum formula in the form relevant to the dyadic ordering weight. -/
theorem twoUnitOrderingWeight_eq_two_mul_sub_digitSum (j : ℕ) :
    twoUnitOrderingWeight j = 2 * j - (Nat.digits 2 j).sum := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) j
  norm_num at h
  rw [twoUnitOrderingWeight, h]
  have hd := Nat.digit_sum_le 2 j
  omega

/-- Legendre's digit-sum formula in the form relevant to the triadic ordering weight.
The factor `2` avoids a truncated division in the exact identity. -/
theorem two_mul_threeUnitOrderingWeight_eq_three_mul_sub_digitSum (j : ℕ) :
    2 * threeUnitOrderingWeight j =
      3 * (j / 2) - (Nat.digits 3 (j / 2)).sum := by
  have h := sub_one_mul_padicValNat_factorial (p := 3) (j / 2)
  norm_num at h
  rw [threeUnitOrderingWeight, Nat.mul_add, h]
  have hd := Nat.digit_sum_le 3 (j / 2)
  omega

/-- Exact decomposition of a dyadic block gain into its degree and factorial parts. -/
theorem twoUnitBlockGain_eq (s : ℕ) :
    twoUnitBlockGain s =
      s * (s - 1) / 2 +
        ∑ j ∈ Finset.range s, padicValNat 2 j.factorial := by
  simp only [twoUnitBlockGain, twoUnitOrderingWeight, Finset.sum_add_distrib,
    Finset.sum_range_id]

/-- Exact decomposition of a triadic block gain into its half-degree and factorial parts. -/
theorem threeUnitBlockGain_eq (s : ℕ) :
    threeUnitBlockGain s =
      (∑ j ∈ Finset.range s, j / 2) +
        ∑ j ∈ Finset.range s, padicValNat 3 (j / 2).factorial := by
  simp only [threeUnitBlockGain, threeUnitOrderingWeight, Finset.sum_add_distrib]

theorem twoUnitOrderingWeight_le_two_mul (j : ℕ) :
    twoUnitOrderingWeight j ≤ 2 * j := by
  rw [twoUnitOrderingWeight, two_mul]
  exact Nat.add_le_add_left (padicValNat_factorial_le 2 j) j

theorem threeUnitOrderingWeight_le (j : ℕ) :
    threeUnitOrderingWeight j ≤ j := by
  rw [threeUnitOrderingWeight]
  calc
    j / 2 + padicValNat 3 (j / 2).factorial ≤ j / 2 + j / 2 :=
      Nat.add_le_add_left (padicValNat_factorial_le 3 (j / 2)) _
    _ ≤ j := by omega

/-- A dyadic block of size `s` has at most quadratic all-layer unit gain. -/
theorem twoUnitBlockGain_le_square (s : ℕ) :
    twoUnitBlockGain s ≤ s ^ 2 := by
  calc
    twoUnitBlockGain s ≤ ∑ j ∈ Finset.range s, 2 * j := by
      exact Finset.sum_le_sum fun j _ ↦ twoUnitOrderingWeight_le_two_mul j
    _ = 2 * (∑ j ∈ Finset.range s, j) := by
      simp only [Finset.mul_sum]
    _ = s * (s - 1) := by
      rw [mul_comm, Finset.sum_range_id_mul_two]
    _ ≤ s ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_left s (Nat.sub_le s 1)

/-- A triadic block of size `s` has at most half a square of all-layer unit gain,
expressed without natural-number division. -/
theorem two_mul_threeUnitBlockGain_le_square (s : ℕ) :
    2 * threeUnitBlockGain s ≤ s ^ 2 := by
  calc
    2 * threeUnitBlockGain s =
        ∑ j ∈ Finset.range s, 2 * threeUnitOrderingWeight j := by
      simp only [threeUnitBlockGain, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range s, 2 * j := by
      exact Finset.sum_le_sum fun j _ ↦
        Nat.mul_le_mul_left 2 (threeUnitOrderingWeight_le j)
    _ = 2 * (∑ j ∈ Finset.range s, j) := by
      simp only [Finset.mul_sum]
    _ = s * (s - 1) := by
      rw [mul_comm, Finset.sum_range_id_mul_two]
    _ ≤ s ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_left s (Nat.sub_le s 1)

/-- Finite aggregate dyadic bound for an arbitrary family of blocks. -/
theorem sum_twoUnitBlockGain_le_card_mul_square
    {ι : Type*} (I : Finset ι) (s : ι → ℕ) (S : ℕ)
    (hs : ∀ k ∈ I, s k ≤ S) :
    (∑ k ∈ I, twoUnitBlockGain (s k)) ≤ I.card * S ^ 2 := by
  calc
    (∑ k ∈ I, twoUnitBlockGain (s k)) ≤ ∑ _k ∈ I, S ^ 2 := by
      exact Finset.sum_le_sum fun k hk ↦
        (twoUnitBlockGain_le_square (s k)).trans
          (Nat.pow_le_pow_left (hs k hk) 2)
    _ = I.card * S ^ 2 := by simp

/-- Finite aggregate triadic bound for an arbitrary family of blocks. -/
theorem two_mul_sum_threeUnitBlockGain_le_card_mul_square
    {ι : Type*} (I : Finset ι) (s : ι → ℕ) (S : ℕ)
    (hs : ∀ k ∈ I, s k ≤ S) :
    2 * (∑ k ∈ I, threeUnitBlockGain (s k)) ≤ I.card * S ^ 2 := by
  calc
    2 * (∑ k ∈ I, threeUnitBlockGain (s k)) =
        ∑ k ∈ I, 2 * threeUnitBlockGain (s k) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _k ∈ I, S ^ 2 := by
      exact Finset.sum_le_sum fun k hk ↦
        (two_mul_threeUnitBlockGain_le_square (s k)).trans
          (Nat.pow_le_pow_left (hs k hk) 2)
    _ = I.card * S ^ 2 := by simp

/-- If both the number of dyadic blocks and every block size are at most `S`, their
aggregate all-layer unit gain is at most `S ^ 3`. -/
theorem sum_twoUnitBlockGain_le_cube
    {ι : Type*} (I : Finset ι) (s : ι → ℕ) (S : ℕ)
    (hcard : I.card ≤ S) (hs : ∀ k ∈ I, s k ≤ S) :
    (∑ k ∈ I, twoUnitBlockGain (s k)) ≤ S ^ 3 := by
  calc
    (∑ k ∈ I, twoUnitBlockGain (s k)) ≤ I.card * S ^ 2 :=
      sum_twoUnitBlockGain_le_card_mul_square I s S hs
    _ ≤ S * S ^ 2 := Nat.mul_le_mul_right _ hcard
    _ = S ^ 3 := by ring

/-- If both the number of triadic blocks and every block size are at most `S`, twice their
aggregate all-layer unit gain is at most `S ^ 3`. -/
theorem two_mul_sum_threeUnitBlockGain_le_cube
    {ι : Type*} (I : Finset ι) (s : ι → ℕ) (S : ℕ)
    (hcard : I.card ≤ S) (hs : ∀ k ∈ I, s k ≤ S) :
    2 * (∑ k ∈ I, threeUnitBlockGain (s k)) ≤ S ^ 3 := by
  calc
    2 * (∑ k ∈ I, threeUnitBlockGain (s k)) ≤ I.card * S ^ 2 :=
      two_mul_sum_threeUnitBlockGain_le_card_mul_square I s S hs
    _ ≤ S * S ^ 2 := Nat.mul_le_mul_right _ hcard
    _ = S ^ 3 := by ring

end LeanProofs.TwoBaseIntegerExponent
