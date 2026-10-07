/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_degreeOf_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial κ ℝ)) (j : κ) (e : ℕ)
    (hM : ∀ a b, (M a b).degreeOf j ≤ e) :
    M.det.degreeOf j ≤ Fintype.card ι * e := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro σ _
  have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial κ ℝ)) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
  rw [hsign]
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  calc
    _ ≤ ∑ _a : ι, e := Finset.sum_le_sum (fun a _ => hM (σ a) a)
    _ = _ := by simp

theorem polynomial_det_value_abs_lower {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial κ ℝ)) (x : κ → ℝ) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i, c ≤ |a i|) :
    c ^ Fintype.card ι ≤ |MvPolynomial.eval x M.det| := by
  rw [(MvPolynomial.eval x).map_det]
  change c ^ Fintype.card ι ≤ |(M.map (MvPolynomial.eval x)).det|
  rw [hdiag, Matrix.det_diagonal, Finset.abs_prod]
  calc
    c ^ Fintype.card ι = ∏ _i : ι, c := by simp
    _ ≤ ∏ i : ι, |a i| := Finset.prod_le_prod₀ (fun _ _ => hc) (fun index _ => ha index)

end Erdos3

end

end OAI
