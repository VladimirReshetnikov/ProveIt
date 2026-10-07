import OAI.Combinatorics.Progressions.Dynamics.PivotDeterminantBudget

namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def normalizedIntegerPivot (A : Matrix I I ℤ) (S P : I → ℝ) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * A.map (Int.castRingHom ℝ) * Matrix.diagonal S

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem normalizedIntegerPivot_abs_det (A : Matrix I I ℤ) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    |(normalizedIntegerPivot A S P).det| =
      (A.det.natAbs : ℝ) * (∏ i, S i) / (∏ i, P i) := by
  have hprodS : 0 < ∏ i, S i := Finset.prod_pos fun i _ => hS i
  have hprodP : 0 < ∏ i, P i := Finset.prod_pos fun i _ => hP i
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  simp only [normalizedIntegerPivot, Matrix.det_mul, Matrix.det_diagonal,
    hd, Finset.prod_inv_distrib, abs_mul, abs_inv, abs_of_pos hprodS, abs_of_pos hprodP,
    Nat.cast_natAbs, Int.cast_abs, div_eq_mul_inv]
  ring

theorem normalizedIntegerPivot_det_ne_zero (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedIntegerPivot A S P).det ≠ 0 := by
  apply abs_pos.mp
  rw [normalizedIntegerPivot_abs_det A S P hS hP]
  have hq : (0 : ℝ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  exact div_pos (mul_pos hq (Finset.prod_pos fun i _ => hS i))
    (Finset.prod_pos fun i _ => hP i)

theorem pivotGrid_normalization_factor {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    ((∏ i, P i) / (∏ i, S i)) *
        (Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) : ℝ) /
        (m.natAbs : ℝ) ^ Fintype.card J =
      ((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det| := by
  have hprodS : (∏ i, S i) ≠ 0 := (Finset.prod_pos fun i _ => hS i).ne'
  have hprodP : (∏ i, P i) ≠ 0 := (Finset.prod_pos fun i _ => hP i).ne'
  have hq : (A.det.natAbs : ℝ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr hA
  have hm' : (m.natAbs : ℝ) ^ Fintype.card J ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Int.natAbs_ne_zero.mpr hm)
  have hc : (Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) : ℝ) * A.det.natAbs =
      (m.natAbs : ℝ) ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index := by
    exact_mod_cast pivotFiberGrid_card_mul A hA B hm hdiv
  rw [normalizedIntegerPivot_abs_det A S P hS hP]
  field_simp
  nlinarith [hc]

end Erdos3

end

end OAI
