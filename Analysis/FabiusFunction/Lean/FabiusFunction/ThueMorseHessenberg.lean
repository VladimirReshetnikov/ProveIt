import FabiusFunction.ThueMorseEulerTransform
import FabiusFunction.ToeplitzHessenberg

/-!
# The Hessenberg determinant formula for the Thue–Morse sign

The ruler-convolution recurrence packages the signs `ε(1), …, ε(n)` into the
convolution system of `FabiusFunction.ToeplitzHessenberg`, whose triangular
matrix has diagonal `1, 2, …, n` and Toeplitz band the ruler coefficients
`a_k = 2^(ν₂(k)+1) - 1`.  The general Toeplitz–Hessenberg determinant formula
`det_hessBand_of_recurrence` then evaluates the atlas's Hessenberg matrix
`H_n` outright — no determinant expansion, and no linear algebra beyond what
that module already provides.

* `rulerCoeff` — the Euler-transform coefficient `a_k = 2^(ν₂(k)+1) - 1`.
* `thueMorseTriangular` / `thueMorseHessenberg` — the system matrix `T_n` and
  the atlas's Hessenberg matrix `H_n`, as instances of `triBand` / `hessBand`.
* `thueMorseSign_ruler_recurrence` — the ruler convolution in the scalar form
  the general formula consumes.
* `thueMorseTriangular_mulVec` — the same recurrence in system form: the
  ruler convolution as the linear system
  `T_n·(ε(1),…,ε(n)) = (-a_1,…,-a_n)`.
* `det_thueMorseTriangular` — `det T_n = n!`.
* `det_thueMorseHessenberg` — **the determinant formula**
  `det H_n = (-1)^n·n!·ε(n)` (`eq:Hessenberg-factorial`), valid for all `n`
  including `n = 0`; hence `det H_n = ±n!`
  (`det_thueMorseHessenberg_eq_or`), and the same fact in `ℕ`-valued form
  `|det H_n| = n!` (`natAbs_det_thueMorseHessenberg`).  Both of the latter
  drop the sign, so both are weaker than the determinant formula itself.
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

/-- The ruler coefficient `a_k = 2^(ν₂(k)+1) - 1` of the Euler transform. -/
def rulerCoeff (k : ℕ) : ℤ := 2 ^ (padicValNat 2 k + 1) - 1

/-- The diagonal `1, 2, 3, …` of the ruler convolution system. -/
private def rulerDiag (m : ℕ) : ℤ := (m : ℤ) + 1

/-- The lower-triangular system matrix of the ruler convolution: diagonal
`1, 2, …, n`, and `a_(m-j)` below the diagonal. -/
def thueMorseTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  triBand n rulerDiag rulerCoeff

/-- The atlas's Hessenberg matrix `H_n`: ruler coefficients `a_(i-j+1)` on and
below the diagonal, superdiagonal `1, 2, …, n-1`. -/
def thueMorseHessenberg (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  hessBand n rulerDiag rulerCoeff

/-- Entrywise formula for the lower-triangular Thue–Morse ruler-convolution
matrix. -/
theorem thueMorseTriangular_apply (n : ℕ) (m j : Fin n) :
    thueMorseTriangular n m j =
      if (j : ℕ) = (m : ℕ) then ((m : ℕ) + 1 : ℤ)
      else if (j : ℕ) < (m : ℕ) then rulerCoeff ((m : ℕ) - (j : ℕ)) else 0 :=
  rfl

/-- Entrywise formula for the Thue–Morse ruler-coefficient Hessenberg matrix. -/
theorem thueMorseHessenberg_apply (n : ℕ) (i j : Fin n) :
    thueMorseHessenberg n i j =
      if (j : ℕ) = (i : ℕ) + 1 then ((i : ℕ) + 1 : ℤ)
      else if (j : ℕ) ≤ (i : ℕ) then rulerCoeff ((i : ℕ) - (j : ℕ) + 1)
      else 0 :=
  rfl

private theorem prod_range_rulerDiag (n : ℕ) :
    ∏ i ∈ range n, rulerDiag i = (n.factorial : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, rulerDiag]
      push_cast
      ring

/-- The determinant of the system matrix is `n!`. -/
theorem det_thueMorseTriangular (n : ℕ) :
    (thueMorseTriangular n).det = (n.factorial : ℤ) := by
  rw [thueMorseTriangular, det_triBand, prod_range_rulerDiag]

/-- **The ruler convolution as a scalar recurrence.**  For every `m`,

`(m+1)·ε(m+1) + ∑_{j<m} a_(m-j)·ε(j+1) = -a_(m+1)`.

This is `ruler_convolution` at `m + 1`, with the convolution sum over
`1 ≤ k ≤ m + 1` re-indexed by reflection so that the last term is split
off. -/
theorem thueMorseSign_ruler_recurrence (m : ℕ) :
    rulerDiag m * thueMorseSign (m + 1) +
        ∑ j ∈ range m, rulerCoeff (m - j) * thueMorseSign (j + 1) =
      -rulerCoeff (m + 1) := by
  have hruler := ruler_convolution (m + 1)
  have hIcc : ∑ k ∈ Finset.Icc 1 (m + 1),
      ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (m + 1 - k) =
      ∑ j ∈ range m, rulerCoeff (m - j) * thueMorseSign (j + 1) +
        rulerCoeff (m + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ]
    congr 1
    · rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.mp hj
      rw [show 1 + (m - 1 - j) = m - j by omega,
        show m + 1 - (m - j) = j + 1 by omega]
      rfl
    · rw [show m + 1 - (1 + m) = 0 by omega]
      have hzero : thueMorseSign 0 = 1 := by
        simp [thueMorseSign, binaryWeight]
      rw [hzero, mul_one, show 1 + m = m + 1 by omega]
      rfl
  rw [hIcc] at hruler
  rw [rulerDiag]
  push_cast at hruler
  linarith [hruler]

/-- **The ruler convolution in system form**: `T_n` applied to the sign
vector `(ε(1), …, ε(n))` returns `(-a_1, …, -a_n)`.  This is the matrix
reading of `thueMorseSign_ruler_recurrence`, row by row; the determinant
formula below consumes the scalar form directly, so nothing depends on
this statement. -/
theorem thueMorseTriangular_mulVec (n : ℕ) :
    (thueMorseTriangular n).mulVec
        (fun j : Fin n => thueMorseSign ((j : ℕ) + 1)) =
      fun m : Fin n => -rulerCoeff ((m : ℕ) + 1) := by
  funext m
  have h : (thueMorseTriangular n).mulVec
      (fun j : Fin n => thueMorseSign ((j : ℕ) + 1)) m =
      rulerDiag (m : ℕ) * thueMorseSign ((m : ℕ) + 1) +
        ∑ j ∈ range (m : ℕ),
          rulerCoeff ((m : ℕ) - j) * thueMorseSign (j + 1) :=
    triBand_mulVec_apply n rulerDiag rulerCoeff
      (fun j => thueMorseSign (j + 1)) m
  rw [h]
  exact thueMorseSign_ruler_recurrence (m : ℕ)

/-- **The Hessenberg determinant formula** (`eq:Hessenberg-factorial`):
`det H_n = (-1)^n·n!·ε(n)`, for every `n ≥ 0`. -/
theorem det_thueMorseHessenberg (n : ℕ) :
    (thueMorseHessenberg n).det =
      (-1) ^ n * (n.factorial : ℤ) * thueMorseSign n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : thueMorseSign 0 = 1 := by simp [thueMorseSign, binaryWeight]
    simp [hzero]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [thueMorseHessenberg,
    det_hessBand_of_recurrence N rulerDiag rulerCoeff
      (fun j => thueMorseSign (j + 1))
      (fun m _ => thueMorseSign_ruler_recurrence m),
    prod_range_rulerDiag]

/-- The Hessenberg determinant is `±n!`. -/
theorem det_thueMorseHessenberg_eq_or (n : ℕ) :
    (thueMorseHessenberg n).det = (n.factorial : ℤ) ∨
      (thueMorseHessenberg n).det = -(n.factorial : ℤ) := by
  have key : (thueMorseHessenberg n).det =
      (-1 : ℤ) ^ (n + binaryWeight n) * (n.factorial : ℤ) := by
    rw [det_thueMorseHessenberg, thueMorseSign, pow_add]
    ring
  rcases Nat.even_or_odd (n + binaryWeight n) with hp | hp
  · exact Or.inl (by rw [key, hp.neg_one_pow, one_mul])
  · exact Or.inr (by rw [key, hp.neg_one_pow]; ring)

/-- The two-case statement in `ℕ`-valued form: the Hessenberg determinant
has absolute value exactly `n!`.  Through `Int.natAbs_eq_iff` this is
equivalent to `det_thueMorseHessenberg_eq_or`, not a strengthening of it;
both forget the sign that `det_thueMorseHessenberg` pins down.  It is
recorded for consumers that work with `Int.natAbs`. -/
theorem natAbs_det_thueMorseHessenberg (n : ℕ) :
    (thueMorseHessenberg n).det.natAbs = n.factorial := by
  rcases det_thueMorseHessenberg_eq_or n with h | h <;> rw [h] <;> simp

end Fabius
