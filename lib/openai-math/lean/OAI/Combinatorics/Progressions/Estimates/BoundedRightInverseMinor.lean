/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.RectangularDetExpansion
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem submatrix_columns_injective_of_det_ne_zero {I J : Type*}
    [Fintype I] [DecidableEq I] (A : Matrix I J ℝ) (p : I → J)
    (hp : (A.submatrix id p).det ≠ 0) : Function.Injective p := by
  intro i j hij
  by_contra hne
  apply hp
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])

theorem boundedRightInverse_exists_minor {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Nonempty J]
    (A : Matrix I J ℝ) (B : Matrix J I ℝ) (hAB : A * B = 1)
    {Q : ℝ} (hQ : 0 < Q) (hB : ∀ j i, |B j i| ≤ Q) :
    ∃ p : I → J, Function.Injective p ∧
      1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I) ≤
        |(A.submatrix id p).det| := by
  classical
  have hM : (0 : ℝ) < Fintype.card (I → J) := by exact_mod_cast Fintype.card_pos
  have hpow : 0 < Q ^ Fintype.card I := pow_pos hQ _
  have hsum : 1 ≤ ∑ p : I → J, |(A.submatrix id p).det| * Q ^ Fintype.card I := by
    calc
      1 = |∑ p : I → J, (A.submatrix id p).det * ∏ i, B (p i) i| := by
        rw [← rectangular_det_expansion, hAB, Matrix.det_one, abs_one]
      _ ≤ ∑ p : I → J, |(A.submatrix id p).det * ∏ i, B (p i) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul, Finset.abs_prod]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hprod : (∏ i : I, |B (p i) i|) ≤ ∏ _i : I, Q :=
          Finset.prod_le_prod₀ (fun index _ => abs_nonneg (B (p index) index))
            (fun index _ => hB (p index) index)
        simpa only [Finset.prod_const, Finset.card_univ] using hprod
  have hconstant : (∑ _p : I → J, (Fintype.card (I → J) : ℝ)⁻¹) = 1 := by
    simp
  obtain ⟨p, _, hp⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (hconstant.trans_le hsum)
  have hdet : 1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I) ≤
      |(A.submatrix id p).det| := by
    have := (div_le_iff₀ hpow).mpr hp
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, one_mul, mul_comm] using this
  refine ⟨p, submatrix_columns_injective_of_det_ne_zero A p ?_, hdet⟩
  exact abs_pos.mp ((by positivity : 0 <
    1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I)).trans_le hdet)

theorem boundedRightInverse_exists_controlled_pivot {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Nonempty J]
    (A : Matrix I J ℝ) (B : Matrix J I ℝ) (hAB : A * B = 1)
    {H Q : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H)
    (hQ : 0 < Q) (hB : ∀ j i, |B j i| ≤ Q) :
    ∃ p : I → J, Function.Injective p ∧
      (matrixSupCLM (A.submatrix id p)).IsInvertible ∧
      ‖(matrixSupCLM (A.submatrix id p)).inverse‖ ≤
        Fintype.card I * (((Fintype.card I).factorial * H ^ (Fintype.card I - 1)) /
          (1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I))) := by
  obtain ⟨p, hp, hd⟩ := boundedRightInverse_exists_minor A B hAB hQ hB
  have hM : (0 : ℝ) < Fintype.card (I → J) := by exact_mod_cast Fintype.card_pos
  refine ⟨p, hp, matrixSupCLM_inverse_norm_le (A.submatrix id p) hH
    (fun i j => hA i (p j)) (by positivity) hd⟩

end Erdos3

end

end OAI
