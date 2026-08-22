import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeRepulsion

/-!
# Superfactorial content of arbitrary-node interpolation determinants

For `r + 1` integer nodes, the interpolation determinant with columns

`1, x, ..., x ^ (r - 1), y`

is divisible by `0! 1! ... (r - 1)!`.  In Mathlib's convention this divisor is
`Nat.superFactorial (r - 1)`.  Expanding along the last column reduces the assertion to
`Matrix.superFactorial_dvd_vandermonde_det` on each deleted-node Vandermonde minor.

The second half of the file threads this stronger integer lower bound through the existing
arbitrary-node divided-difference argument.  As in `ArbitraryNodeRepulsion`, the determinant
factorization is unconditional and the generalized divided-difference mean-value theorem is
kept as the explicit hypothesis `RpowDividedDifferenceMeanValue`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set
open scoped Nat

noncomputable section

/-- The universal content of an interpolation determinant with `r` ordinary-power columns:
`0! 1! ... (r - 1)!`.  Mathlib's `superFactorial n` is `1! 2! ... n!`, so the index is
`r - 1`. -/
def interpolationSuperfactorial (r : ℕ) : ℕ :=
  (r - 1).superFactorial

@[simp] theorem interpolationSuperfactorial_zero : interpolationSuperfactorial 0 = 1 := by
  simp [interpolationSuperfactorial]

@[simp] theorem interpolationSuperfactorial_one : interpolationSuperfactorial 1 = 1 := by
  simp [interpolationSuperfactorial]

@[simp] theorem interpolationSuperfactorial_succ (r : ℕ) :
    interpolationSuperfactorial (r + 1) = r.superFactorial := by
  simp [interpolationSuperfactorial]

/-- Deleting the last column of the integral interpolation matrix and any one row leaves the
ordinary Vandermonde matrix on the remaining nodes. -/
theorem nodeIntMatrix_lastColumnMinor_eq_vandermonde (r : ℕ)
    (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ) (i : Fin (r + 1)) :
    (nodeIntMatrix r m z).submatrix i.succAbove (Fin.last r).succAbove =
      Matrix.vandermonde (fun j : Fin r ↦ (m (i.succAbove j) : ℤ)) := by
  ext a b
  rw [Matrix.submatrix_apply, Matrix.vandermonde_apply]
  rw [nodeIntMatrix_apply_of_ne]
  congr 1
  simp
  intro h
  have hval := congrArg Fin.val h
  exact (Nat.ne_of_lt b.isLt) (by simpa using hval)

/-- **Universal superfactorial divisor.**  For arbitrary integer nodes and ordinates,
`0! 1! ... (r - 1)!` divides the interpolation determinant. -/
theorem interpolationSuperfactorial_dvd_nodeIntMatrix_det (r : ℕ)
    (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ) :
    (interpolationSuperfactorial r : ℤ) ∣ (nodeIntMatrix r m z).det := by
  cases r with
  | zero => simp [nodeIntMatrix]
  | succ r =>
      rw [Matrix.det_succ_column (nodeIntMatrix (r + 1) m z) (Fin.last (r + 1))]
      apply Finset.dvd_sum
      intro i hi
      refine dvd_mul_of_dvd_right ?_ _
      rw [nodeIntMatrix_lastColumnMinor_eq_vandermonde]
      simpa using Matrix.superFactorial_dvd_vandermonde_det
        (fun j : Fin (r + 1) ↦ (m (i.succAbove j) : ℤ))

/-- Consecutive nodes used to show that the universal divisor is sharp. -/
def consecutiveInterpolationNodes (r : ℕ) : Fin (r + 1) → ℕ :=
  fun i ↦ i

/-- The ordinate vector supported only at the last consecutive node. -/
def lastInterpolationOrdinate (r : ℕ) : Fin (r + 1) → ℤ :=
  fun i ↦ if i = Fin.last r then 1 else 0

/-- **Sharpness of the universal divisor.**  At the consecutive nodes `0, ..., r`, with the
ordinate vector supported at `r`, the interpolation determinant is exactly the universal
superfactorial. -/
theorem det_nodeIntMatrix_consecutive_lastOrdinate (r : ℕ) :
    (nodeIntMatrix r (consecutiveInterpolationNodes r) (lastInterpolationOrdinate r)).det =
      (interpolationSuperfactorial r : ℤ) := by
  cases r with
  | zero => simp [nodeIntMatrix, consecutiveInterpolationNodes, lastInterpolationOrdinate]
  | succ r =>
      rw [Matrix.det_succ_column
        (nodeIntMatrix (r + 1) (consecutiveInterpolationNodes (r + 1))
          (lastInterpolationOrdinate (r + 1))) (Fin.last (r + 1))]
      rw [Finset.sum_eq_single (Fin.last (r + 1))]
      · rw [nodeIntMatrix_apply_last]
        simp only [lastInterpolationOrdinate, if_pos, mul_one]
        rw [nodeIntMatrix_lastColumnMinor_eq_vandermonde]
        rw [show ((-1 : ℤ) ^
            ((Fin.last (r + 1) : ℕ) + (Fin.last (r + 1) : ℕ))) = 1 by
          simp [Fin.val_last], one_mul]
        have hnodes :
            (fun j : Fin (r + 1) ↦
              (consecutiveInterpolationNodes (r + 1)
                ((Fin.last (r + 1)).succAbove j) : ℤ)) =
              fun j : Fin (r + 1) ↦ (j : ℤ) := by
          funext j
          simp [consecutiveInterpolationNodes]
        rw [hnodes, Matrix.det_vandermonde_id_eq_superFactorial (R := ℤ)]
        simp [interpolationSuperfactorial]
      · intro i hi hne
        rw [nodeIntMatrix_apply_last]
        simp [lastInterpolationOrdinate, hne]
      · intro hnotmem
        exact (hnotmem (Finset.mem_univ _)).elim

/-! ## Candidate-node determinants -/

/-- The real candidate-node determinant is the cast of an integer divisible by the universal
superfactorial. -/
theorem exists_int_det_nodeMatrix_and_superfactorial_dvd (r : ℕ)
    (m : Fin (r + 1) → ℕ) (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) :
    ∃ D : ℤ, (D : ℝ) = (nodeMatrix r m).det ∧
      (interpolationSuperfactorial r : ℤ) ∣ D := by
  have hz : ∀ i : Fin (r + 1),
      ∃ z : ℤ, (z : ℝ) = (m i : ℝ) ^ logThreeDivLogTwo :=
    fun i ↦ (hcand i).2
  choose z hzeq using hz
  refine ⟨(nodeIntMatrix r m z).det, ?_,
    interpolationSuperfactorial_dvd_nodeIntMatrix_det r m z⟩
  rw [Int.cast_det, nodeIntMatrix_map r m z hzeq]

/-- **Superfactorial lower bound.**  A nonzero candidate-node determinant has absolute value
at least `0! 1! ... (r - 1)!`, strengthening the generic integral lower bound `1`. -/
theorem interpolationSuperfactorial_le_abs_det_nodeMatrix (r : ℕ)
    (m : Fin (r + 1) → ℕ) (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hne : (nodeMatrix r m).det ≠ 0) :
    (interpolationSuperfactorial r : ℝ) ≤ |(nodeMatrix r m).det| := by
  obtain ⟨D, hD, hdiv⟩ := exists_int_det_nodeMatrix_and_superfactorial_dvd r m hcand
  have hDne : D ≠ 0 := by
    intro hzero
    apply hne
    rw [← hD, hzero]
    norm_num
  have hInt : (interpolationSuperfactorial r : ℤ) ≤ |D| :=
    Int.le_abs_of_dvd hDne hdiv
  calc
    (interpolationSuperfactorial r : ℝ) = ((interpolationSuperfactorial r : ℤ) : ℝ) := by
      norm_num
    _ ≤ (|D| : ℤ) := by exact_mod_cast hInt
    _ = |(D : ℝ)| := by norm_num
    _ = |(nodeMatrix r m).det| := by rw [hD]

/-- The determinant/divided-difference bridge with the superfactorial lower bound retained.
This theorem is algebraic: the divided-difference factorization and upper bound are explicit
hypotheses. -/
theorem interpolationSuperfactorial_le_vandermondeProduct_mul_of_dividedDifference
    (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) {dd B : ℝ}
    (hdet : (nodeMatrix r m).det = vandermondeProduct r m * dd)
    (hdd_bound : |dd| ≤ B) (hne : (nodeMatrix r m).det ≠ 0) :
    (interpolationSuperfactorial r : ℝ) ≤ vandermondeProduct r m * B := by
  have hV : 0 < vandermondeProduct r m := vandermondeProduct_pos r m hstrict
  have hlo := interpolationSuperfactorial_le_abs_det_nodeMatrix r m hcand hne
  have hhi : |(nodeMatrix r m).det| ≤ |vandermondeProduct r m| * B :=
    abs_det_nodeMatrix_le_of_dividedDifference r m hdet hdd_bound
  rw [abs_of_pos hV] at hhi
  exact hlo.trans hhi

/-- Packaged superfactorial repulsion from an arbitrary positive divided-difference bound.
Compared with `inv_le_vandermondeProduct_of_dividedDifference`, the lower bound gains the
factor `interpolationSuperfactorial r`. -/
theorem interpolationSuperfactorial_mul_inv_le_vandermondeProduct_of_dividedDifference
    (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) {dd B : ℝ}
    (hB : 0 < B) (hdet : (nodeMatrix r m).det = vandermondeProduct r m * dd)
    (hdd_bound : |dd| ≤ B) (hne : (nodeMatrix r m).det ≠ 0) :
    (interpolationSuperfactorial r : ℝ) * B⁻¹ ≤ vandermondeProduct r m := by
  have h := interpolationSuperfactorial_le_vandermondeProduct_mul_of_dividedDifference
    r m hstrict hcand hdet hdd_bound hne
  have hinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  calc
    (interpolationSuperfactorial r : ℝ) * B⁻¹
        ≤ (vandermondeProduct r m * B) * B⁻¹ :=
      mul_le_mul_of_nonneg_right h hinv
    _ = vandermondeProduct r m := by field_simp

/-! ## Strengthened arbitrary-node repulsion -/

/-- **Superfactorial arbitrary-node repulsion.**  Conditional only on the same explicit
divided-difference mean-value property as `le_vandermondeProduct_of_dividedDiffMeanValue`,

`SF(r) * r! / |(θ)_r| * m₀ ^ (r - θ) ≤ ∏ᵢ<ⱼ (mⱼ - mᵢ)`.
-/
theorem superfactorial_mul_le_vandermondeProduct_of_dividedDiffMeanValue {r : ℕ}
    (hr : 2 ≤ r) (m : Fin (r + 1) → ℕ) (hstrict : StrictMono m)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hmv : RpowDividedDifferenceMeanValue logThreeDivLogTwo r
      (fun i ↦ (m i : ℝ))) :
    (interpolationSuperfactorial r : ℝ) *
        ((r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
          (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo)) ≤
      vandermondeProduct r m := by
  obtain ⟨xi, hxi0, -, hddval⟩ := hmv
  have hcne : fallingRpowCoeff logThreeDivLogTwo r ≠ 0 :=
    fallingRpowCoeff_logThreeDivLogTwo_ne_zero r
  have hcpos : 0 < |fallingRpowCoeff logThreeDivLogTwo r| := abs_pos.mpr hcne
  have hFpos : (0 : ℝ) < (r ! : ℝ) := by exact_mod_cast r.factorial_pos
  have hm0pos : (0 : ℝ) < (m 0 : ℝ) := by exact_mod_cast (hcand 0).1
  have hxipos : (0 : ℝ) < xi := hm0pos.trans hxi0
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hexp : logThreeDivLogTwo - (r : ℝ) < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  let B : ℝ := |fallingRpowCoeff logThreeDivLogTwo r| *
    (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) / (r ! : ℝ)
  have hBpos : 0 < B := by
    exact div_pos (mul_pos hcpos (Real.rpow_pos_of_pos hm0pos _)) hFpos
  have hpow : xi ^ (logThreeDivLogTwo - (r : ℝ)) ≤
      (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm0pos hxi0.le hexp.le
  have hbound :
      |dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo)| ≤ B := by
    rw [hddval, abs_div, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hxipos (logThreeDivLogTwo - (r : ℝ))),
      abs_of_pos hFpos]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hFpos.le
  have hdet := det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff r m hstrict
  have hddne :
      dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo) ≠ 0 := by
    rw [hddval]
    exact div_ne_zero (mul_ne_zero hcne (Real.rpow_pos_of_pos hxipos _).ne') hFpos.ne'
  have hVpos : 0 < vandermondeProduct r m := vandermondeProduct_pos r m hstrict
  have hdetne : (nodeMatrix r m).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero hVpos.ne' hddne
  have hmain :=
    interpolationSuperfactorial_mul_inv_le_vandermondeProduct_of_dividedDifference
      r m hstrict hcand hBpos hdet hbound hdetne
  have hpowInv :
      ((m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)))⁻¹ =
        (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) := by
    rw [← Real.rpow_neg hm0pos.le]
    congr 1
    ring
  have hBinv : B⁻¹ =
      (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) := by
    dsimp [B]
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_rev, hpowInv]
    field_simp
  rwa [hBinv] at hmain

/-- **Superfactorial local packing.**  If `r + 1` candidate nodes lie in `[N,N+H]`, then
the old packing lower bound gains the universal factor `0! 1! ... (r-1)!`. -/
theorem superfactorial_packing_of_dividedDiffMeanValue {r : ℕ} (hr : 2 ≤ r)
    (m : Fin (r + 1) → ℕ) (hstrict : StrictMono m)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hmv : RpowDividedDifferenceMeanValue logThreeDivLogTwo r
      (fun i ↦ (m i : ℝ)))
    {N H : ℝ} (hN : 1 ≤ N) (hlo : ∀ i, N ≤ (m i : ℝ))
    (hhi : ∀ i, (m i : ℝ) ≤ N + H) :
    (interpolationSuperfactorial r : ℝ) *
        ((r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
          N ^ ((r : ℝ) - logThreeDivLogTwo)) ≤ H ^ pairCount r := by
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hexp : (0 : ℝ) ≤ (r : ℝ) - logThreeDivLogTwo := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hcoef : 0 ≤ (interpolationSuperfactorial r : ℝ) *
      ((r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r|) := by positivity
  have hpow : N ^ ((r : ℝ) - logThreeDivLogTwo) ≤
      (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) :=
    Real.rpow_le_rpow hNpos.le (hlo 0) hexp
  calc
    (interpolationSuperfactorial r : ℝ) *
        ((r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
          N ^ ((r : ℝ) - logThreeDivLogTwo))
        ≤ (interpolationSuperfactorial r : ℝ) *
          ((r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
            (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo)) := by
          have := mul_le_mul_of_nonneg_left hpow hcoef
          ring_nf at this ⊢
          exact this
    _ ≤ vandermondeProduct r m :=
      superfactorial_mul_le_vandermondeProduct_of_dividedDiffMeanValue
        hr m hstrict hcand hmv
    _ ≤ H ^ pairCount r := vandermondeProduct_le_pow r m hstrict hlo hhi

end

end LeanProofs.TwoBaseIntegerExponent
