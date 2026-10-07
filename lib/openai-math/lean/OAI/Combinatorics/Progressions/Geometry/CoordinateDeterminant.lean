import Mathlib.Analysis.Calculus.MeanValue
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDegree
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound

namespace OAI

section

namespace Erdos3

noncomputable def coordinateMatrixPolynomial {I X : Type*} (index : I → I → X) :
    Matrix I I (MvPolynomial X ℝ) := fun i j => MvPolynomial.X (index i j)

theorem coordinateMatrixPolynomial_eval {I X : Type*} [Fintype I] [DecidableEq I]
    (index : I → I → X) (x : X → ℝ) :
    MvPolynomial.eval x (coordinateMatrixPolynomial index).det =
      Matrix.det (fun i j => x (index i j)) := by
  rw [(MvPolynomial.eval x).map_det]
  congr 1
  ext i j
  change MvPolynomial.eval x (MvPolynomial.X (index i j) : MvPolynomial X ℝ) = x (index i j)
  simp only [MvPolynomial.eval_X]

theorem coordinateMatrixPolynomial_degree {I X : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq X] (index : I → I → X) (j : X) :
    (coordinateMatrixPolynomial index).det.degreeOf j ≤ Fintype.card I := by
  apply (polynomial_det_degreeOf_le _ j 1 ?_).trans_eq (Nat.mul_one _)
  intro a b
  simp only [coordinateMatrixPolynomial, MvPolynomial.degreeOf_X]
  split_ifs <;> omega

noncomputable def coordinateDeterminantVariation (I X : Type*) [Fintype I] [Fintype X] : ℝ :=
  Fintype.card X * ((Fintype.card I).factorial * Fintype.card I)

theorem coordinateDeterminantVariation_nonneg (I X : Type*) [Fintype I] [Fintype X] :
    0 ≤ coordinateDeterminantVariation I X := by
  unfold coordinateDeterminantVariation
  positivity

theorem coordinateMatrixPolynomial_derivative {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (index : I → I → X) (x : X → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (coordinateMatrixPolynomial index).det) x‖ ≤
      coordinateDeterminantVariation I X := by
  have h := polynomial_det_fderiv_norm_le (coordinateMatrixPolynomial index) x
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X] using hx (index a b))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [one_pow, mul_one, coordinateDeterminantVariation] using h

theorem coordinateMatrixPolynomial_variation {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (index : I → I → X) (x y : X → ℝ) (hx : ∀ j, |x j| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    |MvPolynomial.eval x (coordinateMatrixPolynomial index).det -
        MvPolynomial.eval y (coordinateMatrixPolynomial index).det| ≤
      coordinateDeterminantVariation I X * ‖x - y‖ := by
  let S : Set (X → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hmem (z : X → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 1 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (coordinateMatrixPolynomial index).det).differentiable
      (by norm_num) z)
    (fun z hz => coordinateMatrixPolynomial_derivative index z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

end Erdos3

end

end OAI
