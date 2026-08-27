import FabiusFunction.ThueMorseEulerTransform
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The Hessenberg determinant formula for the Thue–Morse sign

The ruler-convolution recurrence packages the signs `ε(1), …, ε(n)`
into a lower-triangular linear system with diagonal `1, 2, …, n`.
Cramer's rule then evaluates `n!·ε(n)` as the determinant of the system
matrix with its last column replaced by the right-hand side, and one
cyclic column rotation turns that matrix into the atlas's Hessenberg
matrix `H_n` — no determinant expansion is ever performed.

* `cramer_mulVec` — reusable linear algebra, for any commutative ring:
  `A.cramer (A *ᵥ x) = A.det • x` (Cramer's rule applied to a vector
  already known to be a solution).
* `thueMorseTriangular` / `thueMorseHessenberg` — the system matrix
  `T_n` and the atlas's Hessenberg matrix `H_n`
  (`a_k = 2^(ν₂(k)+1) - 1` on and below the diagonal, superdiagonal
  `1, 2, …, n-1`).
* `thueMorseTriangular_mulVec` — the ruler convolution as the linear
  system `T_n·(ε(1),…,ε(n)) = (-a_1,…,-a_n)`.
* `det_thueMorseTriangular` — `det T_n = n!`.
* `det_thueMorseHessenberg` — **the determinant formula**
  `det H_n = (-1)^n·n!·ε(n)` (`eq:Hessenberg-factorial`), valid for all
  `n` including `n = 0`; hence `det H_n = ±n!`
  (`det_thueMorseHessenberg_eq_or`).
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

/-- **Cramer's rule for a known solution**, over any commutative ring:
the Cramer map applied to `A *ᵥ x` returns `det A • x`.  (Replacing a
column of `A` by a linear combination of its columns keeps only the
diagonal term of the expanded determinant.) -/
theorem cramer_mulVec {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (A : Matrix n n R) (x : n → R) :
    A.cramer (A.mulVec x) = A.det • x := by
  have hexpand : A.mulVec x = ∑ j, x j • (fun i => A i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hexpand, map_sum]
  funext i
  have hterm : ∀ j, A.cramer (fun k => A k j) =
      (Pi.single j A.det : n → R) :=
    fun j => Matrix.cramer_row_self A _ j fun k => rfl
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    hterm, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg fun h => hj h.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The ruler coefficient `a_k = 2^(ν₂(k)+1) - 1` of the Euler
transform. -/
def rulerCoeff (k : ℕ) : ℤ := 2 ^ (padicValNat 2 k + 1) - 1

/-- The lower-triangular system matrix of the ruler convolution:
diagonal `1, 2, …, n`, and `a_(m-j)` below the diagonal. -/
def thueMorseTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun m j =>
    if (j : ℕ) = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
    else if (j : ℕ) < (m : ℕ) then rulerCoeff ((m : ℕ) - (j : ℕ)) else 0

/-- The atlas's Hessenberg matrix `H_n`: ruler coefficients `a_(i-j+1)`
on and below the diagonal, superdiagonal `1, 2, …, n-1`. -/
def thueMorseHessenberg (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if (j : ℕ) = (i : ℕ) + 1 then ((i : ℕ) + 1 : ℤ)
    else if (j : ℕ) ≤ (i : ℕ) then rulerCoeff ((i : ℕ) - (j : ℕ) + 1) else 0

/-- The ruler convolution in system form: `T_n` applied to the sign
vector `(ε(1), …, ε(n))` returns `(-a_1, …, -a_n)`. -/
theorem thueMorseTriangular_mulVec (n : ℕ) :
    (thueMorseTriangular n).mulVec
        (fun j : Fin n => thueMorseSign ((j : ℕ) + 1)) =
      fun m : Fin n => -rulerCoeff ((m : ℕ) + 1) := by
  funext m
  simp only [Matrix.mulVec, dotProduct]
  have hfin : ∑ j : Fin n, thueMorseTriangular n m j *
        thueMorseSign ((j : ℕ) + 1) =
      ∑ j ∈ range n,
        (if j = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
          else if j < (m : ℕ) then rulerCoeff ((m : ℕ) - j) else 0) *
          thueMorseSign (j + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
      (if j = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
        else if j < (m : ℕ) then rulerCoeff ((m : ℕ) - j) else 0) *
        thueMorseSign (j + 1)) n]
    rfl
  rw [hfin]
  -- restrict to the nonzero columns `j ≤ m`
  have hsub : ∑ j ∈ range ((m : ℕ) + 1),
      (if j = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
        else if j < (m : ℕ) then rulerCoeff ((m : ℕ) - j) else 0) *
        thueMorseSign (j + 1) =
      ∑ j ∈ range n,
        (if j = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
          else if j < (m : ℕ) then rulerCoeff ((m : ℕ) - j) else 0) *
          thueMorseSign (j + 1) := by
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      have hm := m.isLt
      exact Finset.mem_range.mpr (by omega)
    · intro j _ hj
      have hgt : ¬ j < (m : ℕ) + 1 := fun hc => hj (Finset.mem_range.mpr hc)
      rw [if_neg (by omega), if_neg (by omega), zero_mul]
  rw [← hsub, Finset.sum_range_succ, if_pos rfl]
  -- identify the sub-diagonal part with the ruler-convolution tail
  have hbelow : ∑ j ∈ range (m : ℕ),
      (if j = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
        else if j < (m : ℕ) then rulerCoeff ((m : ℕ) - j) else 0) *
        thueMorseSign (j + 1) =
      ∑ j ∈ range (m : ℕ), rulerCoeff ((m : ℕ) - j) *
        thueMorseSign (j + 1) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [if_neg (by omega), if_pos (by omega)]
  rw [hbelow]
  -- the ruler convolution at `m + 1`
  have hruler := ruler_convolution ((m : ℕ) + 1)
  -- rewrite its `Icc` sum as the reflected range sum
  have hIcc : ∑ k ∈ Finset.Icc 1 ((m : ℕ) + 1),
      ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) *
        thueMorseSign ((m : ℕ) + 1 - k) =
      ∑ j ∈ range (m : ℕ), rulerCoeff ((m : ℕ) - j) *
        thueMorseSign (j + 1) + rulerCoeff ((m : ℕ) + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ]
    congr 1
    · rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.mp hj
      rw [show 1 + ((m : ℕ) - 1 - j) = (m : ℕ) - j by omega,
        show (m : ℕ) + 1 - ((m : ℕ) - j) = j + 1 by omega]
      rfl
    · rw [show (m : ℕ) + 1 - (1 + (m : ℕ)) = 0 by omega]
      have hzero : thueMorseSign 0 = 1 := by
        simp [thueMorseSign, binaryWeight]
      rw [hzero, mul_one, show 1 + (m : ℕ) = (m : ℕ) + 1 by omega]
      rfl
  rw [hIcc] at hruler
  -- assemble: X + (m+1)·ε(m+1) = X + (-(X + a_(m+1))) = -a_(m+1)
  have hcast : (((m : ℕ) + 1 : ℕ) : ℤ) = ((m : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hruler
  rw [hruler]
  ring

private theorem prod_range_cast_add_one (n : ℕ) :
    ∏ i ∈ range n, ((i : ℤ) + 1) = (n.factorial : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring

/-- The determinant of the system matrix is `n!`. -/
theorem det_thueMorseTriangular (n : ℕ) :
    (thueMorseTriangular n).det = (n.factorial : ℤ) := by
  have htri : (thueMorseTriangular n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    have : (i : ℕ) < (j : ℕ) := hlt
    simp only [thueMorseTriangular]
    rw [if_neg (by omega), if_neg (by omega)]
  rw [Matrix.det_of_lowerTriangular _ htri]
  have hdiag : ∀ i : Fin n, thueMorseTriangular n i i = ((i : ℕ) + 1 : ℤ) := by
    intro i
    simp [thueMorseTriangular]
  rw [Finset.prod_congr rfl fun i _ => hdiag i,
    Fin.prod_univ_eq_prod_range (fun i => ((i : ℤ) + 1)) n]
  exact prod_range_cast_add_one n

private theorem hessenberg_col_zero (N : ℕ) (i : Fin (N + 1)) :
    thueMorseHessenberg (N + 1) i 0 = rulerCoeff ((i : ℕ) + 1) := by
  simp only [thueMorseHessenberg]
  rw [show ((0 : Fin (N + 1)) : ℕ) = 0 from rfl]
  rw [if_neg (by omega), if_pos (by omega), Nat.sub_zero]

/-- **The Hessenberg determinant formula** (`eq:Hessenberg-factorial`):
`det H_n = (-1)^n·n!·ε(n)`, for every `n ≥ 0`. -/
theorem det_thueMorseHessenberg (n : ℕ) :
    (thueMorseHessenberg n).det =
      (-1) ^ n * (n.factorial : ℤ) * thueMorseSign n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : thueMorseSign 0 = 1 := by simp [thueMorseSign, binaryWeight]
    simp [hzero]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  -- Cramer at the last column of the triangular system
  have hcram : ((thueMorseTriangular (N + 1)).updateCol (Fin.last N)
        (fun m : Fin (N + 1) => -rulerCoeff ((m : ℕ) + 1))).det =
      ((N + 1).factorial : ℤ) * thueMorseSign (N + 1) := by
    have h := congrFun (cramer_mulVec (thueMorseTriangular (N + 1))
      (fun j : Fin (N + 1) => thueMorseSign ((j : ℕ) + 1))) (Fin.last N)
    rw [thueMorseTriangular_mulVec (N + 1), Matrix.cramer_apply,
      det_thueMorseTriangular] at h
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul, Fin.val_last]
  -- the column rotation: S = H'.submatrix id (finRotate (N+1)),
  -- where H' is the Hessenberg matrix with its first column negated
  have hrot : ((thueMorseHessenberg (N + 1)).updateCol 0
        (fun i => -thueMorseHessenberg (N + 1) i 0)).submatrix id
        (finRotate (N + 1)) =
      (thueMorseTriangular (N + 1)).updateCol (Fin.last N)
        (fun m : Fin (N + 1) => -rulerCoeff ((m : ℕ) + 1)) := by
    funext i j
    simp only [Matrix.submatrix_apply, id_eq, finRotate_apply]
    by_cases hj : j = Fin.last N
    · subst hj
      rw [Fin.last_add_one]
      rw [Matrix.updateCol_apply, if_pos rfl,
        Matrix.updateCol_apply, if_pos rfl,
        hessenberg_col_zero]
    · have hjlt : (j : ℕ) < N := by
        have := j.isLt
        rcases Nat.lt_or_ge (j : ℕ) N with h | h
        · exact h
        · exact absurd (Fin.ext (by rw [Fin.val_last]; omega) :
            j = Fin.last N) hj
      have hval : ((j + 1 : Fin (N + 1)) : ℕ) = (j : ℕ) + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hne0 : (j + 1 : Fin (N + 1)) ≠ 0 := by
        intro h
        have := congrArg (fun t : Fin (N + 1) => (t : ℕ)) h
        simp only [hval, Fin.val_zero] at this
        omega
      have hnelast : j ≠ Fin.last N := hj
      rw [Matrix.updateCol_apply, if_neg hne0,
        Matrix.updateCol_apply, if_neg hnelast]
      simp only [thueMorseHessenberg, thueMorseTriangular, hval]
      split_ifs with h1 h2 h3 h4 h5 <;> first
        | rfl
        | omega
        | (congr 1; omega)
  -- determinant bookkeeping
  have hupd : (thueMorseHessenberg (N + 1)).updateCol 0
      (fun i => thueMorseHessenberg (N + 1) i 0) =
      thueMorseHessenberg (N + 1) := by
    funext i j
    rw [Matrix.updateCol_apply]
    split_ifs with h
    · subst h; rfl
    · rfl
  have hdetH' : ((thueMorseHessenberg (N + 1)).updateCol 0
        (fun i => -thueMorseHessenberg (N + 1) i 0)).det =
      -(thueMorseHessenberg (N + 1)).det := by
    have hsmul : (fun i => -thueMorseHessenberg (N + 1) i 0) =
        (-1 : ℤ) • (fun i => thueMorseHessenberg (N + 1) i 0) := by
      funext i
      simp
    rw [hsmul, Matrix.det_updateCol_smul, hupd]
    ring
  have hperm := Matrix.det_permute' (finRotate (N + 1))
    ((thueMorseHessenberg (N + 1)).updateCol 0
      (fun i => -thueMorseHessenberg (N + 1) i 0))
  rw [hrot, hcram, hdetH', sign_finRotate] at hperm
  -- hperm : (N+1)!·ε(N+1) = ((-1)^N : ℤˣ)·(-(det H))
  have hsq : ((-1 : ℤ) ^ N) * ((-1 : ℤ) ^ N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one] at hperm
  have hmul : ((-1 : ℤ) ^ N) *
      (((N + 1).factorial : ℤ) * thueMorseSign (N + 1)) =
      -(thueMorseHessenberg (N + 1)).det := by
    rw [hperm, ← mul_assoc, hsq, one_mul]
  have hdetH : (thueMorseHessenberg (N + 1)).det =
      -((-1 : ℤ) ^ N * (((N + 1).factorial : ℤ) * thueMorseSign (N + 1))) := by
    omega
  rw [hdetH, pow_succ]
  ring

/-- The Hessenberg determinant is `±n!`. -/
theorem det_thueMorseHessenberg_eq_or (n : ℕ) :
    (thueMorseHessenberg n).det = (n.factorial : ℤ) ∨
      (thueMorseHessenberg n).det = -(n.factorial : ℤ) := by
  have h := det_thueMorseHessenberg n
  rcases Nat.even_or_odd (n + binaryWeight n) with hpar | hpar
  · left
    rw [h, thueMorseSign]
    rcases Nat.even_or_odd n with hn | hn
    · have hw : Even (binaryWeight n) := by
        rcases hpar with ⟨t, ht⟩
        rcases hn with ⟨s, hs⟩
        exact ⟨t - s, by omega⟩
      rw [hn.neg_one_pow, hw.neg_one_pow]
      ring
    · have hw : Odd (binaryWeight n) := by
        rcases hpar with ⟨t, ht⟩
        rcases hn with ⟨s, hs⟩
        exact ⟨t - s - 1, by omega⟩
      rw [hn.neg_one_pow, hw.neg_one_pow]
      ring
  · right
    rw [h, thueMorseSign]
    rcases Nat.even_or_odd n with hn | hn
    · have hw : Odd (binaryWeight n) := by
        rcases hpar with ⟨t, ht⟩
        rcases hn with ⟨s, hs⟩
        exact ⟨t - s, by omega⟩
      rw [hn.neg_one_pow, hw.neg_one_pow]
      ring
    · have hw : Even (binaryWeight n) := by
        rcases hpar with ⟨t, ht⟩
        rcases hn with ⟨s, hs⟩
        exact ⟨t - s, by omega⟩
      rw [hn.neg_one_pow, hw.neg_one_pow]
      ring

end Fabius
