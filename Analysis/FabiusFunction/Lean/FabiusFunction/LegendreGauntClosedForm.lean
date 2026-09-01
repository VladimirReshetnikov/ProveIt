import FabiusFunction.LegendreGaunt

/-!
# Closed form for Legendre Gaunt coefficients

This module identifies the executable rational Gaunt coefficient with twice
the square of the zero-row Wigner `3j` datum.  Since Mathlib currently has no
Wigner-symbol API, the squared zero-row datum is defined here directly by its
total rational central-binomial formula.  The definition is zero off the
parity-and-triangle support.

The proof is internal to the Legendre development.  Its boundary value is
read from the leading coefficient in the exact product linearization, and a
private rational Bonnet recurrence propagates that value through the triangle
coordinates.  Thus no analytic integral evaluation or external
representation-theory assertion is assumed.

Only the squared integer-index zero-row datum is treated.  This module makes
no signed-symbol or Condon--Shortley phase choice, and develops no half-integer
or nonzero-magnetic-index symbols, general `3j`/`6j`/`9j` theory, Wigner
orthogonality, or recoupling identities.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

/-! ## Total zero-row square datum and its support -/

/-- The parity-and-weak-triangle support of a zero-row Legendre Gaunt
coefficient. -/
def legendreGauntAdmissible (i j k : ℕ) : Prop :=
  (i + j + k) % 2 = 0 ∧ i ≤ j + k ∧ j ≤ i + k ∧ k ≤ i + j

private instance legendreGauntAdmissibleDecidable (i j k : ℕ) :
    Decidable (legendreGauntAdmissible i j k) := by
  unfold legendreGauntAdmissible
  infer_instance

/-- The total rational square of the zero-row Wigner `3j` datum.  On the
admissible support it is the central-binomial quotient in the three triangle
coordinates; off that support it is zero.  This is a square datum only: no
choice of sign or phase for a Wigner symbol is made. -/
def legendreWignerThreeJZeroSqRat (i j k : ℕ) : ℚ :=
  if legendreGauntAdmissible i j k then
    let s := (i + j + k) / 2
    (((s - i).centralBinom : ℕ) : ℚ) *
        (((s - j).centralBinom : ℕ) : ℚ) *
        (((s - k).centralBinom : ℕ) : ℚ) /
      (((2 * s + 1 : ℕ) : ℚ) * ((s.centralBinom : ℕ) : ℚ))
  else 0

/-- Admissibility is equivalent to the existence of the three triangle
coordinates `a`, `b`, and `c`, with indices their pairwise sums. -/
theorem legendreGauntAdmissible_iff_exists_pairwise_add (i j k : ℕ) :
    legendreGauntAdmissible i j k ↔
      ∃ a b c : ℕ, i = b + c ∧ j = a + c ∧ k = a + b := by
  constructor
  · rintro ⟨heven, hi, hj, hk⟩
    obtain ⟨s, hs⟩ : ∃ s, i + j + k = 2 * s := by
      use (i + j + k) / 2
      omega
    refine ⟨s - i, s - j, s - k, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨a, b, c, rfl, rfl, rfl⟩
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- Every triple of pairwise sums is admissible. -/
theorem legendreGauntAdmissible_pairwise_add (a b c : ℕ) :
    legendreGauntAdmissible (b + c) (a + c) (a + b) := by
  rw [legendreGauntAdmissible_iff_exists_pairwise_add]
  exact ⟨a, b, c, rfl, rfl, rfl⟩

/-- In triangle coordinates the total zero-row square datum is the symmetric
central-binomial quotient. -/
theorem legendreWignerThreeJZeroSqRat_pairwise_add (a b c : ℕ) :
    legendreWignerThreeJZeroSqRat (b + c) (a + c) (a + b) =
      ((a.centralBinom : ℕ) : ℚ) *
          ((b.centralBinom : ℕ) : ℚ) *
          ((c.centralBinom : ℕ) : ℚ) /
        (((2 * (a + b + c) + 1 : ℕ) : ℚ) *
          (((a + b + c).centralBinom : ℕ) : ℚ)) := by
  rw [legendreWignerThreeJZeroSqRat,
    if_pos (legendreGauntAdmissible_pairwise_add a b c)]
  have hs : ((b + c + (a + c) + (a + b)) / 2) = a + b + c := by omega
  rw [hs]
  dsimp only
  rw [show a + b + c - (b + c) = a by omega,
    show a + b + c - (a + c) = b by omega,
    show a + b + c - (a + b) = c by omega]

private lemma cast_centralBinom_eq_factorial (n : ℕ) :
    ((n.centralBinom : ℕ) : ℚ) =
      (((2 * n).factorial : ℕ) : ℚ) /
        (((n.factorial : ℕ) : ℚ) ^ 2) := by
  rw [Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℚ (show n ≤ 2 * n by omega)]
  rw [show 2 * n - n = n by omega]
  ring

/-- In triangle coordinates the zero-row square datum has the classical
factorial form. -/
theorem legendreWignerThreeJZeroSqRat_pairwise_add_factorial (a b c : ℕ) :
    legendreWignerThreeJZeroSqRat (b + c) (a + c) (a + b) =
      (((a + b + c).factorial : ℕ) : ℚ) ^ 2 *
          (((2 * a).factorial : ℕ) : ℚ) *
          (((2 * b).factorial : ℕ) : ℚ) *
          (((2 * c).factorial : ℕ) : ℚ) /
        ((((2 * (a + b + c) + 1).factorial : ℕ) : ℚ) *
          (((a.factorial : ℕ) : ℚ) ^ 2) *
          (((b.factorial : ℕ) : ℚ) ^ 2) *
          (((c.factorial : ℕ) : ℚ) ^ 2)) := by
  rw [legendreWignerThreeJZeroSqRat_pairwise_add,
    cast_centralBinom_eq_factorial a,
    cast_centralBinom_eq_factorial b,
    cast_centralBinom_eq_factorial c,
    cast_centralBinom_eq_factorial (a + b + c)]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Half-sum form of the classical zero-row square factorial formula.  The
hypotheses say that `s` is the half-sum and dominates all three indices. -/
theorem legendreWignerThreeJZeroSqRat_eq_factorial_of_halfSum
    {i j k s : ℕ} (hs : i + j + k = 2 * s)
    (hi : i ≤ s) (hj : j ≤ s) (hk : k ≤ s) :
    legendreWignerThreeJZeroSqRat i j k =
      ((s.factorial : ℕ) : ℚ) ^ 2 *
          (((2 * (s - i)).factorial : ℕ) : ℚ) *
          (((2 * (s - j)).factorial : ℕ) : ℚ) *
          (((2 * (s - k)).factorial : ℕ) : ℚ) /
        ((((2 * s + 1).factorial : ℕ) : ℚ) *
          ((((s - i).factorial : ℕ) : ℚ) ^ 2) *
          ((((s - j).factorial : ℕ) : ℚ) ^ 2) *
          ((((s - k).factorial : ℕ) : ℚ) ^ 2)) := by
  have h_i : (s - j) + (s - k) = i := by omega
  have h_j : (s - i) + (s - k) = j := by omega
  have h_k : (s - i) + (s - j) = k := by omega
  have h_sum : (s - i) + (s - j) + (s - k) = s := by omega
  have h := legendreWignerThreeJZeroSqRat_pairwise_add_factorial
    (s - i) (s - j) (s - k)
  rw [h_sum, h_i, h_j, h_k] at h
  exact h

/-- The total zero-row square datum vanishes outside its admissible support. -/
theorem legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible
    {i j k : ℕ} (h : ¬ legendreGauntAdmissible i j k) :
    legendreWignerThreeJZeroSqRat i j k = 0 := by
  simp [legendreWignerThreeJZeroSqRat, h]

/-! ## Degenerate-triangle boundary -/

private lemma coeff_sum_gaunt_top (i j : ℕ) :
    (∑ k ∈ range (i + j + 1),
        legendreProductLinearizationCoeffRat i j k •
          legendrePolynomialRat k).coeff (i + j) =
      legendreProductLinearizationCoeffRat i j (i + j) *
        (legendrePolynomialRat (i + j)).coeff (i + j) := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (i + j)]
  · simp only [Polynomial.coeff_smul, smul_eq_mul]
  · intro k hk hne
    simp only [Polynomial.coeff_smul, smul_eq_mul]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · rw [natDegree_legendrePolynomialRat]
      have hk' : k < i + j + 1 := Finset.mem_range.mp hk
      omega
  · simp

private lemma coeff_mul_legendrePolynomialRat_top (i j : ℕ) :
    (legendrePolynomialRat i * legendrePolynomialRat j).coeff (i + j) =
      (legendrePolynomialRat i).coeff i *
        (legendrePolynomialRat j).coeff j := by
  calc
    (legendrePolynomialRat i * legendrePolynomialRat j).coeff (i + j) =
        (legendrePolynomialRat i).leadingCoeff *
          (legendrePolynomialRat j).leadingCoeff := by
      simpa only [natDegree_legendrePolynomialRat] using
        Polynomial.coeff_mul_degree_add_degree
          (legendrePolynomialRat i) (legendrePolynomialRat j)
    _ = (legendrePolynomialRat i).coeff i *
          (legendrePolynomialRat j).coeff j := by
      rw [← Polynomial.coeff_natDegree, ← Polynomial.coeff_natDegree,
        natDegree_legendrePolynomialRat, natDegree_legendrePolynomialRat]

/-- The Gaunt coefficient on the degenerate triangle `k = i + j`, in
central-binomial form. -/
theorem legendreGauntRat_add_boundary (i j : ℕ) :
    legendreGauntRat i j (i + j) =
      2 * ((i.centralBinom : ℕ) : ℚ) * ((j.centralBinom : ℕ) : ℚ) /
        (((2 * (i + j) + 1 : ℕ) : ℚ) *
          (((i + j).centralBinom : ℕ) : ℚ)) := by
  have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff (i + j))
    (legendrePolynomialRat_mul_eq_sum_gaunt i j)
  rw [coeff_mul_legendrePolynomialRat_top,
    coeff_sum_gaunt_top] at hcoeff
  rw [legendreProductLinearizationCoeffRat,
    coeff_legendrePolynomialRat_self,
    coeff_legendrePolynomialRat_self,
    coeff_legendrePolynomialRat_self] at hcoeff
  simp only [Nat.centralBinom_eq_two_mul_choose]
  have hpow : (2 : ℚ)⁻¹ ^ i * (2 : ℚ)⁻¹ ^ j =
      (2 : ℚ)⁻¹ ^ (i + j) := by rw [pow_add]
  have hcoeff' :
      (2 : ℚ)⁻¹ ^ (i + j) *
          (((2 * i).choose i : ℕ) : ℚ) *
          (((2 * j).choose j : ℕ) : ℚ) =
        (((2 * (i + j) + 1 : ℕ) : ℚ) / 2) *
          legendreGauntRat i j (i + j) *
          ((2 : ℚ)⁻¹ ^ (i + j) *
            (((2 * (i + j)).choose (i + j) : ℕ) : ℚ)) := by
    calc
      _ = ((2 : ℚ)⁻¹ ^ i * (((2 * i).choose i : ℕ) : ℚ)) *
          ((2 : ℚ)⁻¹ ^ j * (((2 * j).choose j : ℕ) : ℚ)) := by
            rw [← hpow]
            ring
      _ = _ := hcoeff
  have hpowne : (2 : ℚ)⁻¹ ^ (i + j) ≠ 0 := by positivity
  have hcbne : ((((2 * (i + j)).choose (i + j) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (i + j)
  have hoddne : (((2 * (i + j) + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp
  field_simp at hcoeff'
  ring_nf at hcoeff' ⊢
  exact hcoeff'.symm

/-- The zero-row square formula agrees with half the Gaunt coefficient on a
degenerate triangle. -/
theorem legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat
    (i j : ℕ) :
    legendreGauntRat i j (i + j) =
      2 * legendreWignerThreeJZeroSqRat i j (i + j) := by
  rw [legendreGauntRat_add_boundary]
  have hw := legendreWignerThreeJZeroSqRat_pairwise_add j i 0
  simp only [Nat.centralBinom_zero, Nat.cast_one, mul_one] at hw
  have hw' :
      legendreWignerThreeJZeroSqRat i j (i + j) =
        ((i.centralBinom : ℕ) : ℚ) * ((j.centralBinom : ℕ) : ℚ) /
          (((2 * (i + j) + 1 : ℕ) : ℚ) *
            (((i + j).centralBinom : ℕ) : ℚ)) := by
    simpa [add_comm, mul_comm] using hw
  rw [hw']
  ring

/-- If one index is zero, the Gaunt coefficient is the Legendre norm on the
diagonal and zero off it. -/
theorem legendreGauntRat_zero_left (j k : ℕ) :
    legendreGauntRat 0 j k = if j = k then 2 / (((2 * j + 1 : ℕ) : ℚ)) else 0 := by
  split_ifs with h
  · subst k
    have hb := legendreGauntRat_add_boundary 0 j
    simp only [zero_add] at hb
    rw [hb]
    have hcb : ((j.centralBinom : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero j
    field_simp
    norm_num [Nat.centralBinom_zero]
  · by_cases hjk : j < k
    · exact legendreGauntRat_eq_zero_of_add_lt (by omega)
    · rw [legendreGauntRat_swap_right]
      exact legendreGauntRat_eq_zero_of_add_lt (by omega)

/-- The closed zero-row square formula already gives the complete Gaunt
identity when the first index is zero. -/
theorem legendreGauntRat_zero_left_eq_two_mul_wignerThreeJZeroSqRat
    (j k : ℕ) :
    legendreGauntRat 0 j k =
      2 * legendreWignerThreeJZeroSqRat 0 j k := by
  by_cases h : j = k
  · subst k
    simpa using
      legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat 0 j
  · rw [legendreGauntRat_zero_left, if_neg h]
    have hnot : ¬ legendreGauntAdmissible 0 j k := by
      rw [legendreGauntAdmissible_iff_exists_pairwise_add]
      rintro ⟨a, b, c, hi, hj, hk⟩
      omega
    rw [legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible hnot]
    ring

/-! ## Private Bonnet recurrence engine -/

private lemma cast_centralBinom_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * (((n + 1).centralBinom : ℕ) : ℚ) =
      2 * ((2 * n + 1 : ℕ) : ℚ) * ((n.centralBinom : ℕ) : ℚ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

private theorem linearizationCoeff_one_upper (n : ℕ) :
    legendreProductLinearizationCoeffRat 1 n (n + 1) =
      ((n + 1 : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  have hG := legendreGauntRat_add_boundary 1 n
  norm_num [Nat.centralBinom] at hG
  have hG' :
      legendreGauntRat 1 n (n + 1) =
        4 * (((2 * n).choose n : ℕ) : ℚ) /
          (((2 * (n + 1) + 1 : ℕ) : ℚ) *
            (((2 * (n + 1)).choose (n + 1) : ℕ) : ℚ)) := by
    convert hG using 1 <;> norm_num <;> ring
  rw [legendreProductLinearizationCoeffRat, hG']
  norm_num [Nat.centralBinom]
  have hrec := cast_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hodd : ((2 * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcbn : ((n.centralBinom : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero n
  have hcbs : (((n + 1).centralBinom : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (n + 1)
  simp only [Nat.centralBinom_eq_two_mul_choose] at hcbs
  push_cast at hrec ⊢
  field_simp
  field_simp at hrec
  ring_nf at hrec ⊢
  linear_combination -2 * hrec

private theorem linearizationCoeff_one_lower (n : ℕ) :
    legendreProductLinearizationCoeffRat 1 (n + 1) n =
      ((n + 1 : ℕ) : ℚ) / ((2 * (n + 1) + 1 : ℕ) : ℚ) := by
  have hG := legendreGauntRat_add_boundary 1 n
  norm_num [Nat.centralBinom] at hG
  have hG' :
      legendreGauntRat 1 n (n + 1) =
        4 * (((2 * n).choose n : ℕ) : ℚ) /
          (((2 * (n + 1) + 1 : ℕ) : ℚ) *
            (((2 * (n + 1)).choose (n + 1) : ℕ) : ℚ)) := by
    convert hG using 1 <;> norm_num <;> ring
  rw [legendreProductLinearizationCoeffRat,
    legendreGauntRat_swap_right 1 (n + 1) n, hG']
  norm_num [Nat.centralBinom]
  have hrec := cast_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hodd : ((2 * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hodd' : ((2 * (n + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcbn : ((n.centralBinom : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero n
  have hcbs : (((n + 1).centralBinom : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (n + 1)
  simp only [Nat.centralBinom_eq_two_mul_choose] at hcbs
  push_cast at hrec ⊢
  field_simp
  field_simp at hrec
  ring_nf at hrec ⊢
  linear_combination -2 * hrec

private theorem linearizationCoeff_one_eq_zero_other
    {n k : ℕ} (hk : k < n + 2)
    (hup : k ≠ n + 1) (hdown : k ≠ n - 1) :
    legendreProductLinearizationCoeffRat 1 n k = 0 := by
  unfold legendreProductLinearizationCoeffRat
  by_cases htri : 1 + k < n
  · rw [legendreGauntRat_eq_zero_of_triangle_violation
      (Or.inr (Or.inl htri)), mul_zero]
  · have hnpos : 0 < n := by omega
    have hk_eq : k = n := by omega
    subst k
    rw [legendreGauntRat_eq_zero_of_odd_sum]
    · ring
    · exact ⟨n, by omega⟩

private theorem legendrePolynomialRat_zero :
    legendrePolynomialRat 0 = 1 := by
  apply Polynomial.map_injective (Rat.castHom ℝ) (Rat.cast_injective (α := ℝ))
  simp only [legendrePolynomialRat_cast, legendrePolynomial_zero,
    Polynomial.map_one]

private theorem legendrePolynomialRat_one :
    legendrePolynomialRat 1 = X := by
  apply Polynomial.map_injective (Rat.castHom ℝ) (Rat.cast_injective (α := ℝ))
  simp only [legendrePolynomialRat_cast, legendrePolynomial_one,
    Polynomial.map_X]

private theorem legendrePolynomialRat_mul_X (n : ℕ) :
    X * legendrePolynomialRat n =
      (((n + 1 : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ)) •
          legendrePolynomialRat (n + 1) +
        (((n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ)) •
          legendrePolynomialRat (n - 1) := by
  cases n with
  | zero =>
      norm_num [legendrePolynomialRat_zero,
        legendrePolynomialRat_one]
  | succ m =>
      rw [← legendrePolynomialRat_one,
        legendrePolynomialRat_mul_eq_sum_gaunt]
      let s := range (1 + (m + 1) + 1)
      let f : ℕ → ℚ[X] := fun k ↦
        legendreProductLinearizationCoeffRat 1 (m + 1) k •
          legendrePolynomialRat k
      have hup : m + 2 ∈ s := by
        change m + 2 ∈ range (1 + (m + 1) + 1)
        rw [Finset.mem_range]
        omega
      have hdown : m ∈ s.erase (m + 2) := by
        rw [Finset.mem_erase]
        constructor
        · omega
        · simpa only [s, Finset.mem_range] using
            (show m < 1 + (m + 1) + 1 by omega)
      have hzero : ∑ k ∈ (s.erase (m + 2)).erase m, f k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hmem := Finset.mem_erase.mp hk
        have hmem' := Finset.mem_erase.mp hmem.2
        have hkRangeRaw : k < 1 + (m + 1) + 1 := by
          simpa only [s, Finset.mem_range] using hmem'.2
        have hkRange : k < m + 3 := by omega
        have hkUp : k ≠ m + 2 := hmem'.1
        have hkDown : k ≠ m := hmem.1
        change legendreProductLinearizationCoeffRat 1 (m + 1) k •
          legendrePolynomialRat k = 0
        rw [linearizationCoeff_one_eq_zero_other
          (n := m + 1) (k := k) (by omega) (by omega) (by omega), zero_smul]
      calc
        ∑ k ∈ range (1 + (m + 1) + 1),
            legendreProductLinearizationCoeffRat 1 (m + 1) k •
              legendrePolynomialRat k =
            (∑ k ∈ s.erase (m + 2), f k) + f (m + 2) := by
              exact (Finset.sum_erase_add s f hup).symm
        _ = ((∑ k ∈ (s.erase (m + 2)).erase m, f k) + f m) +
              f (m + 2) := by
            rw [Finset.sum_erase_add (s.erase (m + 2)) f hdown]
        _ = f (m + 2) + f m := by rw [hzero]; abel
        _ = (((m + 1 + 1 : ℕ) : ℚ) /
              ((2 * (m + 1) + 1 : ℕ) : ℚ)) •
              legendrePolynomialRat (m + 1 + 1) +
            (((m + 1 : ℕ) : ℚ) / ((2 * (m + 1) + 1 : ℕ) : ℚ)) •
              legendrePolynomialRat (m + 1 - 1) := by
            change legendreProductLinearizationCoeffRat 1 (m + 1) (m + 2) •
                legendrePolynomialRat (m + 2) +
              legendreProductLinearizationCoeffRat 1 (m + 1) m •
                legendrePolynomialRat m = _
            rw [linearizationCoeff_one_upper,
              linearizationCoeff_one_lower]
            congr 2

private theorem gaunt_transfer_recurrence (i j k : ℕ) :
    ((((i + 1 : ℕ) : ℚ)) / (((2 * i + 1 : ℕ) : ℚ))) *
          legendreGauntRat (i + 1) j k +
        ((((i : ℕ) : ℚ)) / (((2 * i + 1 : ℕ) : ℚ))) *
          legendreGauntRat (i - 1) j k =
      ((((j + 1 : ℕ) : ℚ)) / (((2 * j + 1 : ℕ) : ℚ))) *
          legendreGauntRat i (j + 1) k +
        ((((j : ℕ) : ℚ)) / (((2 * j + 1 : ℕ) : ℚ))) *
          legendreGauntRat i (j - 1) k := by
  have hpoly :
      (((((i + 1 : ℕ) : ℚ)) / (((2 * i + 1 : ℕ) : ℚ))) •
            legendrePolynomialRat (i + 1) +
          ((((i : ℕ) : ℚ)) / (((2 * i + 1 : ℕ) : ℚ))) •
            legendrePolynomialRat (i - 1)) *
            legendrePolynomialRat j * legendrePolynomialRat k =
        legendrePolynomialRat i *
          (((((j + 1 : ℕ) : ℚ)) / (((2 * j + 1 : ℕ) : ℚ))) •
              legendrePolynomialRat (j + 1) +
            ((((j : ℕ) : ℚ)) / (((2 * j + 1 : ℕ) : ℚ))) •
              legendrePolynomialRat (j - 1)) * legendrePolynomialRat k := by
    rw [← legendrePolynomialRat_mul_X i,
      ← legendrePolynomialRat_mul_X j]
    ring
  have hmoment := congrArg
    (momentFunctional legendreLebesgueMomentRat) hpoly
  simpa only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, smul_eq_mul,
    ← legendreGauntRat_eq_momentFunctional] using hmoment

private lemma cast_centralBinom_succ_eq (n : ℕ) :
    (((n + 1).centralBinom : ℕ) : ℚ) =
      (2 * ((2 * n + 1 : ℕ) : ℚ) *
        ((n.centralBinom : ℕ) : ℚ)) / ((n + 1 : ℕ) : ℚ) := by
  apply (eq_div_iff (by positivity : (((n + 1 : ℕ) : ℚ)) ≠ 0)).2
  simpa only [mul_comm] using cast_centralBinom_succ n

private def gauntClosedFormCoordinates (a b c : ℕ) : ℚ :=
  2 * ((a.centralBinom : ℕ) : ℚ) *
      ((b.centralBinom : ℕ) : ℚ) *
      ((c.centralBinom : ℕ) : ℚ) /
    (((2 * (a + b + c) + 1 : ℕ) : ℚ) *
      (((a + b + c).centralBinom : ℕ) : ℚ))

private theorem gauntClosedFormCoordinates_transfer_recurrence (a b c : ℕ) :
    (((b + c + 2 : ℕ) : ℚ) /
          ((2 * b + 2 * c + 3 : ℕ) : ℚ)) *
          gauntClosedFormCoordinates a (b + 1) (c + 1) +
        (((b + c + 1 : ℕ) : ℚ) /
          ((2 * b + 2 * c + 3 : ℕ) : ℚ)) *
          gauntClosedFormCoordinates (a + 1) b c =
      (((a + c + 2 : ℕ) : ℚ) /
          ((2 * a + 2 * c + 3 : ℕ) : ℚ)) *
          gauntClosedFormCoordinates (a + 1) b (c + 1) +
        (((a + c + 1 : ℕ) : ℚ) /
          ((2 * a + 2 * c + 3 : ℕ) : ℚ)) *
          gauntClosedFormCoordinates a (b + 1) c := by
  let s := a + b + c
  unfold gauntClosedFormCoordinates
  have hs22 : a + (b + 1) + (c + 1) = s + 2 := by omega
  have hs11a : a + 1 + b + c = s + 1 := by omega
  have hs22a : a + 1 + b + (c + 1) = s + 2 := by omega
  have hs11b : a + (b + 1) + c = s + 1 := by omega
  rw [hs22, hs11a, hs22a, hs11b]
  rw [cast_centralBinom_succ_eq b,
    cast_centralBinom_succ_eq c,
    cast_centralBinom_succ_eq a,
    cast_centralBinom_succ_eq (s + 1),
    cast_centralBinom_succ_eq s]
  have hCs : ((s.centralBinom : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero s
  dsimp only [s] at hCs ⊢
  push_cast
  field_simp [hCs]
  ring

private theorem gaunt_triangle_transfer (a b c : ℕ) :
    (((b + c + 2 : ℕ) : ℚ) /
          ((2 * b + 2 * c + 3 : ℕ) : ℚ)) *
          legendreGauntRat (b + c + 2) (a + c + 1) (a + b + 1) +
        (((b + c + 1 : ℕ) : ℚ) /
          ((2 * b + 2 * c + 3 : ℕ) : ℚ)) *
          legendreGauntRat (b + c) (a + c + 1) (a + b + 1) =
      (((a + c + 2 : ℕ) : ℚ) /
          ((2 * a + 2 * c + 3 : ℕ) : ℚ)) *
          legendreGauntRat (b + c + 1) (a + c + 2) (a + b + 1) +
        (((a + c + 1 : ℕ) : ℚ) /
          ((2 * a + 2 * c + 3 : ℕ) : ℚ)) *
          legendreGauntRat (b + c + 1) (a + c) (a + b + 1) := by
  convert gaunt_transfer_recurrence
    (b + c + 1) (a + c + 1) (a + b + 1) using 1 <;>
      norm_num <;> ring

private theorem legendreGauntRat_pairwise_add_eq_closedForm (a b c : ℕ) :
    legendreGauntRat (b + c) (a + c) (a + b) =
      gauntClosedFormCoordinates a b c := by
  induction c generalizing a b with
  | zero =>
      rw [add_zero, add_zero]
      have hbound :
          legendreGauntRat b a (a + b) =
            2 * ((b.centralBinom : ℕ) : ℚ) *
                ((a.centralBinom : ℕ) : ℚ) /
              (((2 * (a + b) + 1 : ℕ) : ℚ) *
                (((a + b).centralBinom : ℕ) : ℚ)) := by
        convert legendreGauntRat_add_boundary b a using 1 <;>
          norm_num <;> ring
      rw [hbound]
      unfold gauntClosedFormCoordinates
      norm_num [Nat.centralBinom]
      ring
  | succ c ihc =>
      induction b generalizing a with
      | zero =>
          rw [zero_add, add_zero, legendreGauntRat_swap_right]
          have hbound :
              legendreGauntRat (c + 1) a (a + (c + 1)) =
                2 * (((c + 1).centralBinom : ℕ) : ℚ) *
                    ((a.centralBinom : ℕ) : ℚ) /
                  (((2 * (a + (c + 1)) + 1 : ℕ) : ℚ) *
                    (((a + (c + 1)).centralBinom : ℕ) : ℚ)) := by
            convert legendreGauntRat_add_boundary (c + 1) a using 1 <;>
              norm_num <;> ring
          rw [hbound]
          unfold gauntClosedFormCoordinates
          norm_num [Nat.centralBinom]
          congr 1
          ring
      | succ b ihb =>
          have hrec := gaunt_triangle_transfer a b c
          have h2 :
              legendreGauntRat (b + c) (a + c + 1) (a + b + 1) =
                gauntClosedFormCoordinates (a + 1) b c := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ihc (a + 1) b
          have h3 :
              legendreGauntRat (b + c + 1) (a + c + 2) (a + b + 1) =
                gauntClosedFormCoordinates (a + 1) b (c + 1) := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ihb (a + 1)
          have h4 :
              legendreGauntRat (b + c + 1) (a + c) (a + b + 1) =
                gauntClosedFormCoordinates a (b + 1) c := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ihc a (b + 1)
          rw [h2, h3, h4] at hrec
          have hH := gauntClosedFormCoordinates_transfer_recurrence a b c
          have hcoef :
              (((b + c + 2 : ℕ) : ℚ) /
                ((2 * b + 2 * c + 3 : ℕ) : ℚ)) ≠ 0 := by positivity
          have hmain :
              legendreGauntRat (b + c + 2) (a + c + 1) (a + b + 1) =
                gauntClosedFormCoordinates a (b + 1) (c + 1) := by
            apply mul_left_cancel₀ hcoef
            linear_combination hrec - hH
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmain

/-! ## Gaunt--Wigner-square identification -/

/-- In triangle coordinates, the rational Gaunt coefficient is twice the
zero-row Wigner-square datum. -/
theorem legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat
    (a b c : ℕ) :
    legendreGauntRat (b + c) (a + c) (a + b) =
      2 * legendreWignerThreeJZeroSqRat (b + c) (a + c) (a + b) := by
  rw [legendreGauntRat_pairwise_add_eq_closedForm,
    legendreWignerThreeJZeroSqRat_pairwise_add]
  unfold gauntClosedFormCoordinates
  ring

/-- A rational Gaunt coefficient vanishes outside the full parity-and-weak-
triangle support. -/
theorem legendreGauntRat_eq_zero_of_not_admissible
    {i j k : ℕ} (h : ¬ legendreGauntAdmissible i j k) :
    legendreGauntRat i j k = 0 := by
  by_cases heven : (i + j + k) % 2 = 0
  · apply legendreGauntRat_eq_zero_of_triangle_violation
    unfold legendreGauntAdmissible at h
    omega
  · apply legendreGauntRat_eq_zero_of_odd_sum
    refine ⟨(i + j + k) / 2, ?_⟩
    omega

/-- The executable rational Legendre Gaunt coefficient is exactly twice the
total rational zero-row Wigner-square datum. -/
theorem legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat (i j k : ℕ) :
    legendreGauntRat i j k =
      2 * legendreWignerThreeJZeroSqRat i j k := by
  by_cases h : legendreGauntAdmissible i j k
  · rcases (legendreGauntAdmissible_iff_exists_pairwise_add i j k).mp h with
      ⟨a, b, c, rfl, rfl, rfl⟩
    exact legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat a b c
  · rw [legendreGauntRat_eq_zero_of_not_admissible h,
      legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible h]
    ring

/-- The real Gaunt integral is twice the real cast of the rational zero-row
Wigner-square datum. -/
theorem legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat (i j k : ℕ) :
    legendreGaunt i j k =
      2 * (legendreWignerThreeJZeroSqRat i j k : ℝ) := by
  rw [← legendreGauntRat_cast,
    legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat]
  norm_num

/-! ## Sharp support, positivity, and product coefficients -/

/-- The zero-row Wigner-square datum is positive exactly on the admissible
parity-and-triangle support. -/
theorem legendreWignerThreeJZeroSqRat_pos_iff_admissible (i j k : ℕ) :
    0 < legendreWignerThreeJZeroSqRat i j k ↔
      legendreGauntAdmissible i j k := by
  constructor
  · intro hpos
    by_contra h
    rw [legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible h] at hpos
    exact (lt_irrefl 0) hpos
  · intro h
    rcases (legendreGauntAdmissible_iff_exists_pairwise_add i j k).mp h with
      ⟨a, b, c, rfl, rfl, rfl⟩
    rw [legendreWignerThreeJZeroSqRat_pairwise_add]
    have ha : 0 < ((a.centralBinom : ℕ) : ℚ) := by
      exact_mod_cast Nat.centralBinom_pos a
    have hb : 0 < ((b.centralBinom : ℕ) : ℚ) := by
      exact_mod_cast Nat.centralBinom_pos b
    have hc : 0 < ((c.centralBinom : ℕ) : ℚ) := by
      exact_mod_cast Nat.centralBinom_pos c
    have hs : 0 < (((a + b + c).centralBinom : ℕ) : ℚ) := by
      exact_mod_cast Nat.centralBinom_pos (a + b + c)
    positivity

/-- The total rational zero-row Wigner-square datum is nonnegative. -/
theorem legendreWignerThreeJZeroSqRat_nonneg (i j k : ℕ) :
    0 ≤ legendreWignerThreeJZeroSqRat i j k := by
  by_cases h : legendreGauntAdmissible i j k
  · exact (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).2 h |>.le
  · rw [legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible h]

/-- The total rational zero-row Wigner-square datum vanishes exactly outside
the admissible parity-and-triangle support. -/
theorem legendreWignerThreeJZeroSqRat_eq_zero_iff_not_admissible
    (i j k : ℕ) :
    legendreWignerThreeJZeroSqRat i j k = 0 ↔
      ¬ legendreGauntAdmissible i j k := by
  constructor
  · intro hzero hadm
    have hpos :=
      (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).2 hadm
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · exact legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible

/-- The rational Gaunt coefficient is positive exactly on the admissible
parity-and-triangle support. -/
theorem legendreGauntRat_pos_iff_admissible (i j k : ℕ) :
    0 < legendreGauntRat i j k ↔ legendreGauntAdmissible i j k := by
  rw [legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat]
  constructor
  · intro h
    have : 0 < legendreWignerThreeJZeroSqRat i j k := by linarith
    exact (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).1 this
  · intro h
    have := (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).2 h
    positivity

/-- A rational Gaunt coefficient vanishes exactly off the admissible
parity-and-triangle support. -/
theorem legendreGauntRat_eq_zero_iff_not_admissible (i j k : ℕ) :
    legendreGauntRat i j k = 0 ↔ ¬ legendreGauntAdmissible i j k := by
  constructor
  · intro hzero hadm
    have hpos := (legendreGauntRat_pos_iff_admissible i j k).2 hadm
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · exact legendreGauntRat_eq_zero_of_not_admissible

/-- The real Gaunt integral is positive exactly on the admissible parity-and-
triangle support. -/
theorem legendreGaunt_pos_iff_admissible (i j k : ℕ) :
    0 < legendreGaunt i j k ↔ legendreGauntAdmissible i j k := by
  rw [← legendreGauntRat_cast]
  norm_cast
  exact legendreGauntRat_pos_iff_admissible i j k

/-- A real Gaunt integral vanishes exactly outside the admissible parity-and-
triangle support. -/
theorem legendreGaunt_eq_zero_iff_not_admissible (i j k : ℕ) :
    legendreGaunt i j k = 0 ↔ ¬ legendreGauntAdmissible i j k := by
  rw [← legendreGauntRat_cast]
  norm_cast
  exact legendreGauntRat_eq_zero_iff_not_admissible i j k

/-- Every rational Legendre Gaunt coefficient is nonnegative. -/
theorem legendreGauntRat_nonneg (i j k : ℕ) :
    0 ≤ legendreGauntRat i j k := by
  rw [legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat]
  exact mul_nonneg (by norm_num) (legendreWignerThreeJZeroSqRat_nonneg i j k)

/-- Every real Legendre Gaunt integral is nonnegative. -/
theorem legendreGaunt_nonneg (i j k : ℕ) :
    0 ≤ legendreGaunt i j k := by
  rw [← legendreGauntRat_cast]
  exact_mod_cast legendreGauntRat_nonneg i j k

/-- The exact coefficient of `P_k` in `P_i P_j` is `(2k+1)` times the
zero-row Wigner-square datum. -/
theorem legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat
    (i j k : ℕ) :
    legendreProductLinearizationCoeffRat i j k =
      ((2 * k + 1 : ℕ) : ℚ) * legendreWignerThreeJZeroSqRat i j k := by
  rw [legendreProductLinearizationCoeffRat,
    legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat]
  ring

/-- A rational Legendre product-linearization coefficient is positive exactly
on the admissible parity-and-triangle support. -/
theorem legendreProductLinearizationCoeffRat_pos_iff_admissible (i j k : ℕ) :
    0 < legendreProductLinearizationCoeffRat i j k ↔
      legendreGauntAdmissible i j k := by
  rw [legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat]
  constructor
  · intro h
    have hw : 0 < legendreWignerThreeJZeroSqRat i j k := by
      have hk : (0 : ℚ) < ((2 * k + 1 : ℕ) : ℚ) := by positivity
      nlinarith
    exact (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).1 hw
  · intro h
    have hw := (legendreWignerThreeJZeroSqRat_pos_iff_admissible i j k).2 h
    positivity

end Fabius
