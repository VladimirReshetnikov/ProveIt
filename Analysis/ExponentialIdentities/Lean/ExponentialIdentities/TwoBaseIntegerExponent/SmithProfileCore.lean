import ExponentialIdentities.TwoBaseIntegerExponent.GeometricVandermondeSmith
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators
open Finset Matrix

/-- Twice the triangular cost `choose s 2`, written over the integers without division. -/
def twiceTriangular (s : ℕ) : ℤ := (s : ℤ) * ((s : ℤ) - 1)

/-- Twice the determinantal-divisor exponent `mu_m = m^2(m-1)/2`. -/
def twiceSmithMu (m : ℕ) : ℤ := (m : ℤ) ^ 2 * ((m : ℤ) - 1)

/-- The determinantal-divisor exponent `mu_m = m * choose(m,2)`. -/
def smithMu (m : ℕ) : ℕ := m * m.choose 2

theorem twice_choose_two (s : ℕ) :
    (2 : ℤ) * (s.choose 2 : ℤ) = twiceTriangular s := by
  have hs : s.choose 2 * 2 = s * (s - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self s)
  by_cases hs0 : s = 0
  · subst s
    simp [twiceTriangular]
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  calc
    (2 : ℤ) * (s.choose 2 : ℤ) = ((s.choose 2 * 2 : ℕ) : ℤ) := by push_cast; ring
    _ = ((s * (s - 1) : ℕ) : ℤ) := by rw [hs]
    _ = twiceTriangular s := by
      unfold twiceTriangular
      push_cast [Nat.cast_sub hs1]
      rfl

theorem twice_smithMu (m : ℕ) :
    (2 : ℤ) * (smithMu m : ℤ) = twiceSmithMu m := by
  rw [smithMu, Nat.cast_mul]
  calc
    (2 : ℤ) * ((m : ℤ) * (m.choose 2 : ℤ)) =
        (m : ℤ) * (2 * (m.choose 2 : ℤ)) := by ring
    _ = (m : ℤ) * twiceTriangular m := by rw [twice_choose_two]
    _ = twiceSmithMu m := by
      unfold twiceTriangular twiceSmithMu
      ring

/-- Successive determinantal-divisor increments are the doubled Smith exponents
`k(3k+1)`. -/
theorem twiceSmithMu_succ_sub (k : ℕ) :
    twiceSmithMu (k + 1) - twiceSmithMu k =
      (k : ℤ) * (3 * (k : ℤ) + 1) := by
  unfold twiceSmithMu
  push_cast
  ring

/-- Cumulative form of the predicted Smith profile. -/
theorem sum_twiceSmithExponent (m : ℕ) :
    (∑ k ∈ range m, (k : ℤ) * (3 * (k : ℤ) + 1)) = twiceSmithMu m := by
  induction m with
  | zero => simp [twiceSmithMu]
  | succ m ih =>
      rw [sum_range_succ, ih]
      rw [← twiceSmithMu_succ_sub]
      ring

/-- Cauchy/Jensen core of the Smith-profile matching bound.  If `m` positive integers
have total at least `m^2`, their total triangular cost is at least
`m * choose m 2 = m^2(m-1)/2`. -/
theorem twiceSmithMu_le_sum_twiceTriangular
    {m : ℕ} (s : Fin m → ℕ)
    (hs_sum : m ^ 2 ≤ ∑ i, s i) :
    twiceSmithMu m ≤ ∑ i, twiceTriangular (s i) := by
  by_cases hm : m = 0
  · subst m
    simp [twiceSmithMu]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let S : ℚ := ∑ i, (s i : ℚ)
  let Q : ℚ := ∑ i, (s i : ℚ) ^ 2
  have hS : (m : ℚ) ^ 2 ≤ S := by
    dsimp [S]
    exact_mod_cast hs_sum
  have hmQ : S ^ 2 ≤ (m : ℚ) * Q := by
    dsimp [S, Q]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin m))) (f := fun i => (s i : ℚ)))
  have hmone : (1 : ℚ) ≤ m := by exact_mod_cast hmpos
  have hsecond : 0 ≤ S + (m : ℚ) ^ 2 - m := by nlinarith
  have hprod :
      0 ≤ (S - (m : ℚ) ^ 2) * (S + (m : ℚ) ^ 2 - m) :=
    mul_nonneg (sub_nonneg.mpr hS) hsecond
  have hQ :
      (m : ℚ) * ((m : ℚ) ^ 2 * (m - 1)) ≤
        (m : ℚ) * (Q - S) := by
    nlinarith
  have hcancel : (m : ℚ) ^ 2 * (m - 1) ≤ Q - S := by
    have hmQpos : (0 : ℚ) < m := by exact_mod_cast hmpos
    nlinarith
  have hrewrite :
      Q - S = ∑ i, ((s i : ℚ) * ((s i : ℚ) - 1)) := by
    dsimp [Q, S]
    simp_rw [sq, mul_sub]
    rw [sum_sub_distrib]
    simp
  rw [hrewrite] at hcancel
  exact_mod_cast hcancel

/-- Strict equality case of the convex bound: at fixed total `m^2`, equality occurs only
when every separation equals `m`. -/
theorem twiceSmithMu_lt_sum_twiceTriangular_of_ne
    {m : ℕ} (s : Fin m → ℕ)
    (hs_sum : ∑ i, s i = m ^ 2)
    (hne : ∃ i, s i ≠ m) :
    twiceSmithMu m < ∑ i, twiceTriangular (s i) := by
  let S : ℤ := ∑ i, (s i : ℤ)
  let Q : ℤ := ∑ i, (s i : ℤ) ^ 2
  have hS : S = (m : ℤ) ^ 2 := by
    dsimp [S]
    exact_mod_cast hs_sum
  obtain ⟨i, hi⟩ := hne
  have hipos : 0 < ((s i : ℤ) - (m : ℤ)) ^ 2 := by
    apply sq_pos_of_ne_zero
    exact sub_ne_zero.mpr (by exact_mod_cast hi)
  have hsq : 0 < ∑ j, ((s j : ℤ) - (m : ℤ)) ^ 2 := by
    apply Finset.sum_pos'
    · intro j hj
      exact sq_nonneg _
    · exact ⟨i, Finset.mem_univ i, hipos⟩
  have hlin :
      (∑ j, (2 : ℤ) * (s j : ℤ) * (m : ℤ)) =
        2 * (∑ j, (s j : ℤ)) * m := by
    calc
      (∑ j, (2 : ℤ) * (s j : ℤ) * (m : ℤ)) =
          (∑ j, (2 : ℤ) * (s j : ℤ)) * m := by rw [Finset.sum_mul]
      _ = 2 * (∑ j, (s j : ℤ)) * m := by rw [Finset.mul_sum]
  have htri :
      (∑ j, twiceTriangular (s j)) = Q - S := by
    dsimp [twiceTriangular, Q, S]
    simp_rw [mul_sub, sq]
    rw [sum_sub_distrib]
    simp
  have hsquare_expand :
      (∑ j, ((s j : ℤ) - (m : ℤ)) ^ 2) =
        Q - 2 * S * m + (m : ℤ) ^ 3 := by
    dsimp [Q, S]
    simp_rw [sub_sq, sq]
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hlin]
    ring
  have hdiff :
      (∑ j, twiceTriangular (s j)) - twiceSmithMu m =
        ∑ j, ((s j : ℤ) - (m : ℤ)) ^ 2 := by
    rw [htri, hsquare_expand, hS]
    unfold twiceSmithMu
    ring
  nlinarith

/-- Sharp lower bound on the sum of `m` distinct nonnegative integer indices. -/
theorem sum_range_le_sum_injective_fin
    {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) :
    (∑ k ∈ range m, (k : ℤ)) ≤ ∑ i, ((f i : ℕ) : ℤ) := by
  let g : Fin m → ℤ := fun i => ((f i : ℕ) : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    change (((f i : Fin n) : ℕ) : ℤ) = (((f j : Fin n) : ℕ) : ℤ) at hij
    apply hf
    apply Fin.ext
    exact_mod_cast hij
  let s : Finset ℤ := Finset.univ.image g
  have hcard : #s = m := by
    rw [show s = Finset.univ.image g from rfl,
      Finset.card_image_of_injective _ hg]
    simp
  have hsnonneg : ∀ x ∈ s, (0 : ℤ) ≤ x := by
    intro x hx
    simp only [s, mem_image, mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [g]
  have hsharp := Finset.sum_range_le_sum (s := s) (c := (0 : ℤ)) hsnonneg
  rw [hcard] at hsharp
  simpa [s, g, hg] using hsharp

/-- Sharp upper bound on the sum of `m` distinct indices below `n`. -/
theorem sum_injective_fin_le_reverse_range
    {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) :
    (∑ i, ((f i : ℕ) : ℤ)) ≤
      ∑ k ∈ range m, ((n : ℤ) - 1 - k) := by
  let g : Fin m → ℤ := fun i => ((f i : ℕ) : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    change (((f i : Fin n) : ℕ) : ℤ) = (((f j : Fin n) : ℕ) : ℤ) at hij
    apply hf
    apply Fin.ext
    exact_mod_cast hij
  let s : Finset ℤ := Finset.univ.image g
  have hcard : #s = m := by
    rw [show s = Finset.univ.image g from rfl,
      Finset.card_image_of_injective _ hg]
    simp
  have hsupper : ∀ x ∈ s, x ≤ (n : ℤ) - 1 := by
    intro x hx
    simp only [s, mem_image, mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    have hi := (f i).isLt
    change (((f i : Fin n) : ℕ) : ℤ) ≤ (n : ℤ) - 1
    have hiz : (((f i : Fin n) : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast hi
    omega
  have hsharp := Finset.sum_le_sum_range (s := s) (c := (n : ℤ) - 1) hsupper
  rw [hcard] at hsharp
  simpa [s, g, hg] using hsharp

theorem int_sum_range_mul_two (m : ℕ) :
    (∑ k ∈ range m, (k : ℤ)) * 2 = (m : ℤ) * ((m : ℤ) - 1) := by
  have h := Finset.sum_range_id_mul_two m
  by_cases hm : m = 0
  · subst m
    simp
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  calc
    (∑ k ∈ range m, (k : ℤ)) * 2 =
        (((∑ k ∈ range m, k) * 2 : ℕ) : ℤ) := by push_cast; rfl
    _ = ((m * (m - 1) : ℕ) : ℤ) := by rw [h]
    _ = (m : ℤ) * ((m : ℤ) - 1) := by
      push_cast [Nat.cast_sub hm1]
      rfl

/-- The positive separation attached to a matched row/column pair. -/
def matchingSeparation {n m : ℕ}
    (row col : Fin m → Fin n) (i : Fin m) : ℕ :=
  n - (row i : ℕ) + (col i : ℕ)

theorem matchingSeparation_pos {n m : ℕ}
    (row col : Fin m → Fin n) (i : Fin m) :
    1 ≤ matchingSeparation row col i := by
  unfold matchingSeparation
  omega

/-- Distinct rows and distinct columns force total matching separation at least `m^2`.
This is the sharp extremal-index input to the Smith-profile matching bound. -/
theorem sq_le_sum_matchingSeparation
    {n m : ℕ} (row col : Fin m → Fin n)
    (hrow : Function.Injective row) (hcol : Function.Injective col) :
    m ^ 2 ≤ ∑ i, matchingSeparation row col i := by
  have hr := sum_injective_fin_le_reverse_range row hrow
  have hc := sum_range_le_sum_injective_fin col hcol
  let T : ℤ := ∑ k ∈ range m, (k : ℤ)
  have hT : T * 2 = (m : ℤ) * ((m : ℤ) - 1) := by
    simpa [T] using int_sum_range_mul_two m
  have hupper :
      (∑ k ∈ range m, ((n : ℤ) - 1 - k)) =
        (m : ℤ) * ((n : ℤ) - 1) - T := by
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    simp [T]
    ring
  rw [hupper] at hr
  have hsep :
      (m : ℤ) ^ 2 ≤
        (m : ℤ) * (n : ℤ) - (∑ i, (((row i : Fin n) : ℕ) : ℤ)) +
          ∑ i, (((col i : Fin n) : ℕ) : ℤ) := by
    nlinarith
  have hcast :
      ((∑ i, matchingSeparation row col i : ℕ) : ℤ) =
        (m : ℤ) * (n : ℤ) - (∑ i, (((row i : Fin n) : ℕ) : ℤ)) +
          ∑ i, (((col i : Fin n) : ℕ) : ℤ) := by
    simp only [matchingSeparation, Nat.cast_sum, Nat.cast_add,
      Nat.cast_sub (Nat.le_of_lt (row _).isLt), sum_add_distrib,
      sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hcast] at hsep
  exact_mod_cast hsep

/-- General convex matching inequality for the canonical lower-Toeplitz cost.
Every partial matching of `m` distinct rows and columns inside an `n`-square has total doubled
triangular cost at least `m^2(m-1)`. -/
theorem twiceSmithMu_le_matchingCost
    {n m : ℕ} (row col : Fin m → Fin n)
    (hrow : Function.Injective row) (hcol : Function.Injective col) :
    twiceSmithMu m ≤
      ∑ i, twiceTriangular (matchingSeparation row col i) := by
  exact twiceSmithMu_le_sum_twiceTriangular
    (matchingSeparation row col)
    (sq_le_sum_matchingSeparation row col hrow hcol)

/-- Undoubled form of the sharp convex matching inequality. -/
theorem smithMu_le_matchingChooseCost
    {n m : ℕ} (row col : Fin m → Fin n)
    (hrow : Function.Injective row) (hcol : Function.Injective col) :
    smithMu m ≤ ∑ i, (matchingSeparation row col i).choose 2 := by
  have h := twiceSmithMu_le_matchingCost row col hrow hcol
  rw [← twice_smithMu] at h
  have hsum :
      (∑ i, twiceTriangular (matchingSeparation row col i)) =
        (2 : ℤ) * ∑ i, ((matchingSeparation row col i).choose 2 : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [twice_choose_two]
  rw [hsum] at h
  have hz :
      (smithMu m : ℤ) ≤
        ∑ i, ((matchingSeparation row col i).choose 2 : ℤ) := by
    nlinarith
  exact_mod_cast hz

/-- Canonical lower-Toeplitz matrix with the strict Newton coefficient weights
`choose (n-r) 2`.  The unit part is left arbitrary. -/
def weightedLowerToeplitz (n : ℕ) (p : ℤ) (u : ℕ → ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if _h : (j : ℕ) ≤ (i : ℕ) then
    p ^ ((n - (i : ℕ) + (j : ℕ)).choose 2) * u ((i : ℕ) - (j : ℕ))
  else 0

/-- Every minor of the canonical weighted lower-Toeplitz matrix has the sharp universal
power divisor `p^mu_m`.  This is the all-minors lower half of the canonical Smith-profile
theorem; no assumption on the coefficient units is needed. -/
theorem pow_smithMu_dvd_weightedLowerToeplitz_minor
    {n m : ℕ} (p : ℤ) (u : ℕ → ℤ)
    (row col : Fin m → Fin n)
    (hrow : Function.Injective row) (hcol : Function.Injective col) :
    p ^ smithMu m ∣
      ((weightedLowerToeplitz n p u).submatrix row col).det := by
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ hσ
  apply dvd_mul_of_dvd_right
  by_cases hall : ∀ i : Fin m, (col i : ℕ) ≤ (row (σ i) : ℕ)
  · let row' : Fin m → Fin n := fun i => row (σ i)
    have hrow' : Function.Injective row' := hrow.comp σ.injective
    have hcost := smithMu_le_matchingChooseCost row' col hrow' hcol
    have hprod :
        (∏ i : Fin m,
            (weightedLowerToeplitz n p u).submatrix row col (σ i) i) =
          p ^ (∑ i : Fin m, (matchingSeparation row' col i).choose 2) *
            ∏ i : Fin m, u ((row' i : ℕ) - (col i : ℕ)) := by
      simp only [Matrix.submatrix_apply, weightedLowerToeplitz, hall, ↓reduceDIte,
        row', matchingSeparation]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    exact dvd_mul_of_dvd_left (pow_dvd_pow p hcost) _
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hentry :
        (weightedLowerToeplitz n p u).submatrix row col (σ i) i = 0 := by
      simp [weightedLowerToeplitz, Matrix.submatrix_apply, Nat.not_le.mpr hi]
    have hzero :
        (∏ j : Fin m,
            (weightedLowerToeplitz n p u).submatrix row col (σ j) j) = 0 := by
      exact Finset.prod_eq_zero (s := Finset.univ) (i := i)
        (Finset.mem_univ i) hentry
    rw [hzero]
    exact dvd_zero _

end LeanProofs.TwoBaseIntegerExponent
