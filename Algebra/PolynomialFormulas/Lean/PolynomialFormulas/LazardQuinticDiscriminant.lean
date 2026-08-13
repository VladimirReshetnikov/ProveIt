import PolynomialFormulas.LazardQuintic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Lazard's depressed-quintic discriminant

This file connects the explicit coefficient formula called `discriminant` in
`LazardQuintic` to Mathlib's polynomial discriminant, which is named
`Polynomial.discr`.  The determinant calculation is reduced from the modified
`9 × 9` Sylvester matrix to a `4 × 4` Schur complement.  It then derives
nonvanishing from separability, and hence from irreducibility in characteristic
zero.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K] [CharZero K]

private theorem sylvesterDeriv_of_natDegree_eq_five {f : K[X]}
    (hf : f.natDegree = 5) :
    f.sylvesterDeriv.reindex (finCongr <| by rw [hf]) (finCongr <| by rw [hf]) =
    !![f.coeff 0, 0, 0, 0, 1*f.coeff 1, 0, 0, 0, 0;
       f.coeff 1, f.coeff 0, 0, 0, 2*f.coeff 2, 1*f.coeff 1, 0, 0, 0;
       f.coeff 2, f.coeff 1, f.coeff 0, 0, 3*f.coeff 3, 2*f.coeff 2,
         1*f.coeff 1, 0, 0;
       f.coeff 3, f.coeff 2, f.coeff 1, f.coeff 0, 4*f.coeff 4,
         3*f.coeff 3, 2*f.coeff 2, 1*f.coeff 1, 0;
       f.coeff 4, f.coeff 3, f.coeff 2, f.coeff 1, 5*f.coeff 5,
         4*f.coeff 4, 3*f.coeff 3, 2*f.coeff 2, 1*f.coeff 1;
       f.coeff 5, f.coeff 4, f.coeff 3, f.coeff 2, 0, 5*f.coeff 5,
         4*f.coeff 4, 3*f.coeff 3, 2*f.coeff 2;
       0, f.coeff 5, f.coeff 4, f.coeff 3, 0, 0, 5*f.coeff 5,
         4*f.coeff 4, 3*f.coeff 3;
       0, 0, f.coeff 5, f.coeff 4, 0, 0, 0, 5*f.coeff 5, 4*f.coeff 4;
       0, 0, 0, 1, 0, 0, 0, 0, 5] := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Polynomial.sylvesterDeriv, hf, OfNat.ofNat_ne_zero, ↓reduceDIte,
    Polynomial.sylvester, Fin.addCases, Nat.add_one_sub_one, Fin.val_castLT, Set.mem_Icc,
    Fin.val_fin_le, Fin.val_subNat, Fin.val_cast, tsub_le_iff_right, coeff_derivative,
    eq_rec_constant, dite_eq_ite, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat,
    Matrix.reindex_apply, finCongr_symm, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_mk, Matrix.updateRow_apply, Fin.mk.injEq, Matrix.of_apply, Fin.mk_le_mk,
    one_mul, Matrix.cons_val', Matrix.cons_val_fin_one]
  have hi' : i ∈ Finset.range 9 := Finset.mem_range.mpr hi
  have hj' : j ∈ Finset.range 9 := Finset.mem_range.mpr hj
  fin_cases hi' <;>
  · simp only [and_true, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      le_add_iff_nonneg_left, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
      Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLeDiff, nonpos_iff_eq_zero,
      OfNat.one_ne_ofNat, ↓reduceIte, zero_add, zero_le]
    fin_cases hj' <;>
      simp [mul_comm, one_add_one_eq_two, (by norm_num : (2 : K) + 1 = 3),
        (by norm_num : (3 : K) + 1 = 4), (by norm_num : (4 : K) + 1 = 5)]

set_option maxHeartbeats 1000000 in
/-- Lazard's explicit formula is exactly Mathlib's polynomial discriminant.

Mathlib calls the polynomial discriminant `Polynomial.discr`; this is the
quantity often called the polynomial discriminant in mathematical prose. -/
theorem discriminant_eq_polynomial_discr (c : DepressedQuintic K) :
    discriminant c = c.polynomial.discr := by
  let M : Matrix (Fin 9) (Fin 9) K :=
    !![c.s, 0,   0,   0,   c.r,   0,     0,     0,   0;
       c.r, c.s, 0,   0,   2*c.q, c.r,   0,     0,   0;
       c.q, c.r, c.s, 0,   3*c.p, 2*c.q, c.r,   0,   0;
       c.p, c.q, c.r, c.s, 0,     3*c.p, 2*c.q, c.r, 0;
       0,   c.p, c.q, c.r, 5,     0,     3*c.p, 2*c.q, c.r;
       1,   0,   c.p, c.q, 0,     5,     0,     3*c.p, 2*c.q;
       0,   1,   0,   c.p, 0,     0,     5,     0,   3*c.p;
       0,   0,   1,   0,   0,     0,     0,     5,   0;
       0,   0,   0,   1,   0,     0,     0,     0,   5]
  have hpoly : c.polynomial.discr = M.det := by
    let e : Fin (c.polynomial.natDegree - 1 + c.polynomial.natDegree) ≃ Fin 9 :=
      finCongr (by simp)
    rw [Polynomial.discr, ← Matrix.det_reindex_self e,
      sylvesterDeriv_of_natDegree_eq_five c.polynomial_natDegree]
    norm_num [M]
  let A : Matrix (Fin 4) (Fin 4) K :=
    !![c.s, 0, 0, 0; c.r, c.s, 0, 0; c.q, c.r, c.s, 0; c.p, c.q, c.r, c.s]
  let B : Matrix (Fin 4) (Fin 5) K :=
    !![c.r, 0, 0, 0, 0; 2*c.q, c.r, 0, 0, 0;
       3*c.p, 2*c.q, c.r, 0, 0; 0, 3*c.p, 2*c.q, c.r, 0]
  let C : Matrix (Fin 5) (Fin 4) K :=
    !![0, c.p, c.q, c.r; 1, 0, c.p, c.q; 0, 1, 0, c.p;
       0, 0, 1, 0; 0, 0, 0, 1]
  let D : Matrix (Fin 5) (Fin 5) K :=
    !![5, 0, 3*c.p, 2*c.q, c.r; 0, 5, 0, 3*c.p, 2*c.q;
       0, 0, 5, 0, 3*c.p; 0, 0, 0, 5, 0; 0, 0, 0, 0, 5]
  let Di : Matrix (Fin 5) (Fin 5) K :=
    !![1/5, 0, -(3*c.p)/25, -(2*c.q)/25,
         -c.r/25 + 9*c.p^2/125;
       0, 1/5, 0, -(3*c.p)/25, -(2*c.q)/25;
       0, 0, 1/5, 0, -(3*c.p)/25;
       0, 0, 0, 1/5, 0;
       0, 0, 0, 0, 1/5]
  let S : Matrix (Fin 4) (Fin 4) K :=
    !![c.s, -(2*c.p*c.r)/25, -(3*c.q*c.r)/25,
         -(4*c.r^2)/25 + 6*c.p^2*c.r/125;
       4*c.r/5, c.s - 4*c.p*c.q/25,
         -(2*c.p*c.r)/25 - 6*c.q^2/25,
         -(11*c.q*c.r)/25 + 12*c.p^2*c.q/125;
       3*c.q/5, 4*c.r/5 - 6*c.p^2/25,
         c.s - 13*c.p*c.q/25,
         -(14*c.p*c.r)/25 - 6*c.q^2/25 + 18*c.p^3/125;
       2*c.p/5, 3*c.q/5, 4*c.r/5 - 6*c.p^2/25,
         c.s - 13*c.p*c.q/25]
  let e : Fin 9 ≃ (Fin 4 ⊕ Fin 5) :=
    (finSumFinEquiv : (Fin 4 ⊕ Fin 5) ≃ Fin (4 + 5)).symm
  have hblocks : M.reindex e e = Matrix.fromBlocks A B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals
      simp only [Matrix.reindex_apply, e, Equiv.symm_symm,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
      fin_cases i <;> fin_cases j <;> rfl
  have hDiD : Di * D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Di, D, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  letI : Invertible D := invertibleOfLeftInverse D Di hDiD
  have hinv : ⅟D = Di := invOf_eq_left_inv hDiD
  have hschur : A - B * Di * C = S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, B, C, Di, S, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring
  have hdetD : D.det = 3125 := by
    simp [D, Matrix.det_succ_row_zero (n := 4),
      Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Fin.succAbove, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    norm_num
  have hdetS : (3125 : K) * S.det = discriminant c := by
    simp [S, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
      Fin.succAbove, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
      discriminant]
    field_simp
    ring
  rw [hpoly]
  symm
  calc
    M.det = (M.reindex e e).det := (Matrix.det_reindex_self e M).symm
    _ = (Matrix.fromBlocks A B C D).det := congrArg Matrix.det hblocks
    _ = D.det * (A - B * ⅟D * C).det := Matrix.det_fromBlocks₂₂ A B C D
    _ = (3125 : K) * S.det := by rw [hinv, hschur, hdetD]
    _ = discriminant c := hdetS

/-- A separable depressed monic quintic has nonzero Mathlib discriminant. -/
theorem polynomial_discr_ne_zero_of_separable (c : DepressedQuintic K)
    (hsep : c.polynomial.Separable) : c.polynomial.discr ≠ 0 := by
  have hres :
      Polynomial.resultant c.polynomial c.polynomial.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hsep
  have hderivDegree : c.polynomial.derivative.natDegree = 4 := by
    rw [Polynomial.natDegree_derivative, c.polynomial_natDegree]
  have hres' :
      Polynomial.resultant c.polynomial c.polynomial.derivative 5 4 ≠ 0 := by
    simpa [c.polynomial_natDegree, hderivDegree] using hres
  have hdegree : 0 < c.polynomial.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, c.polynomial_natDegree]
    norm_num
  have heq := Polynomial.resultant_deriv (f := c.polynomial) hdegree
  rw [c.polynomial_natDegree, c.polynomial_monic.leadingCoeff] at heq
  norm_num at heq
  rw [heq] at hres'
  exact hres'

/-- An irreducible depressed monic quintic has nonzero Mathlib discriminant. -/
theorem polynomial_discr_ne_zero_of_irreducible (c : DepressedQuintic K)
    (h : Irreducible c.polynomial) : c.polynomial.discr ≠ 0 :=
  polynomial_discr_ne_zero_of_separable c h.separable

/-- An irreducible depressed monic quintic makes Lazard's explicit
discriminant formula nonzero. -/
theorem discriminant_ne_zero_of_irreducible (c : DepressedQuintic K)
    (h : Irreducible c.polynomial) : discriminant c ≠ 0 := by
  rw [discriminant_eq_polynomial_discr]
  exact polynomial_discr_ne_zero_of_irreducible c h

end Field

end LeanProofs.PolynomialFormulas.LazardQuintic
