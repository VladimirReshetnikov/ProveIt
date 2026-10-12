import GowersSzemeredi.Proofs05CommonIntegerRuns

/-! Weighted averaging retains a dense rectangle on two sufficiently large
integer-refinement cells. The algebraic selection is independent of primality. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Small rows and columns cannot carry all the mass when their total
capacity is at most half the original dense mass. -/
theorem exists_dense_large_rectangle_cell {M L : Nat}
    (a : Fin M → Real) (b : Fin L → Real) (c : Fin M → Fin L → Real)
    (m n delta ell : Real) (hm : 0 < m) (hn : 0 < n) (hd : 0 < delta) (he : 0 ≤ ell)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hsuma : ∑ i, a i = m) (hsumb : ∑ j, b j = n)
    (hcap : ∀ i j, c i j ≤ a i * b j)
    (hmass : delta * m * n ≤ ∑ i, ∑ j, c i j)
    (hbudget : ell * ((M : Real) * n + (L : Real) * m) ≤ delta * m * n / 2) :
    ∃ i : Fin M, ∃ j : Fin L,
      ell ≤ a i ∧ ell ≤ b j ∧ delta / 4 * a i * b j ≤ c i j := by
  classical
  by_contra hno
  have hcell (i : Fin M) (j : Fin L) :
      c i j ≤ delta / 4 * a i * b j + ell * b j + ell * a i := by
    have h1 : 0 ≤ delta / 4 * a i * b j :=
      mul_nonneg (mul_nonneg (div_nonneg hd.le (by norm_num)) (ha i)) (hb j)
    have h2 : 0 ≤ ell * b j := mul_nonneg he (hb j)
    have h3 : 0 ≤ ell * a i := mul_nonneg he (ha i)
    by_cases hi : ell ≤ a i
    · by_cases hj : ell ≤ b j
      · have hsmall : c i j < delta / 4 * a i * b j :=
          lt_of_not_ge (fun hc => hno ⟨i, j, hi, hj, hc⟩)
        linarith only [hsmall, h2, h3]
      · have hbound := mul_le_mul_of_nonneg_left (le_of_not_ge hj) (ha i)
        have hcap' := hcap i j
        nlinarith only [hbound, hcap', h1, h2]
    · have hbound := mul_le_mul_of_nonneg_right (le_of_not_ge hi) (hb j)
      have hcap' := hcap i j
      linarith only [hbound, hcap', h1, h3]
  have hupper : (∑ i, ∑ j, c i j) ≤
      delta / 4 * m * n + ell * ((M : Real) * n + (L : Real) * m) := by
    calc
      _ ≤ ∑ i, ∑ j, (delta / 4 * a i * b j + ell * b j + ell * a i) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcell i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          hsuma, hsumb, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
  have hpositive : 0 < delta * m * n := mul_pos (mul_pos hd hm) hn
  linarith only [hupper, hmass, hbudget, hpositive]

/-- The two `4*sqrt(m)` refinement budgets suffice for the threshold
`delta*sqrt(m)/16` on either side of the selected dense rectangle. -/
theorem square_root_rectangle_capacity {m delta : Real} {M L : Nat}
    (hm : 0 ≤ m) (hd : 0 ≤ delta)
    (hM : (M : Real) ≤ 4 * Real.sqrt m) (hL : (L : Real) ≤ 4 * Real.sqrt m) :
    (delta * Real.sqrt m / 16) * ((M : Real) * m + (L : Real) * m) ≤
      delta * m * m / 2 := by
  have hs0 := Real.sqrt_nonneg m
  have hs := Real.sq_sqrt hm
  have hsum : (M : Real) + L ≤ 8 * Real.sqrt m := by linarith only [hM, hL]
  have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ delta * Real.sqrt m / 16 * m by positivity)
  calc
    _ = delta * Real.sqrt m / 16 * m * ((M : Real) + L) := by ring
    _ ≤ delta * Real.sqrt m / 16 * m * (8 * Real.sqrt m) := h
    _ = delta * m * (Real.sqrt m ^ 2) / 2 := by ring
    _ = delta * m * m / 2 := by rw [hs]

end LeanProofs.GowersSzemeredi
