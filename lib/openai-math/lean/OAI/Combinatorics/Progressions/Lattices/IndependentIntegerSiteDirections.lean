import Mathlib.Algebra.BigOperators.Fin
import OAI.Combinatorics.Progressions.Estimates.LowerTriangularMinor
import OAI.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_integer_site_directions {α K W : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (hnonfactor : ¬ ∃ M : (Finset α → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p → Λ p = M (VectorPolynomial.siteEvaluation
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ integerCubeWitnessBound (Fintype.card α) H D) ∧
      (∀ s : Finset α, ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      ∃ w : W, Λ ((map (Int.castRingHom ℝ) (∏ i, rowPolynomial (rows i))) ⊗ₜ[ℝ] w) ≠ 0 := by
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_integral_vector_mode_witness
    root difference selection hdet hH hD hroot hdiff Λ h hnonfactor
  subst h
  let rows := fun i : Fin forms.length => polynomialLinearRow (forms.get i)
  have hmem (i : Fin forms.length) : forms.get i ∈ forms := List.get_mem _ _
  have hpoly (i : Fin forms.length) : rowPolynomial (rows i) = forms.get i :=
    (homogeneous_eq_rowPolynomial _ (hforms _ (hmem i)).1).symm
  have hprod : (∏ i : Fin forms.length, rowPolynomial (rows i)) = forms.prod := by
    simp_rw [hpoly]
    rw [← Fin.prod_ofFn, List.ofFn_get]
  refine ⟨rows, ?_, ?_, ?_⟩
  · intro i k
    exact (integer_coefficient_le_mass (forms.get i) (Finsupp.single k 1)).trans (hforms _ (hmem i)).2
  · intro s
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp (hz s)
    refine ⟨i, ?_⟩
    change (∑ k, polynomialLinearRow (forms.get i) k * affineSite root difference s k) = 0
    rw [← homogeneous_eval_eq_row _ (hforms _ (hmem i)).1]
    exact hi
  · rw [hprod]
    exact hΛ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem integer_difference_exists_pivot {K : Type*} [Fintype K] {q : ℕ}
    (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ))) :
    ∃ selection : Fin q → K, (integerDifferencePivot difference selection).det ≠ 0 := by
  let A : Matrix K (Fin q) ℝ := fun k i => difference i k
  obtain ⟨selection, hdet⟩ := exists_nonzero_row_minor A hlin
  have he : A.submatrix selection id = (realDifferencePivot
      (fun i k => (difference i k : ℝ)) selection).transpose := rfl
  rw [he, Matrix.det_transpose, ← integerDifferencePivot_det_cast] at hdet
  exact ⟨selection, fun hz => hdet (by rw [hz, Int.cast_zero])⟩

theorem exists_integer_site_directions_of_independent {K W : Type*} [Fintype K] {q : ℕ}
    [AddCommGroup W] [Module ℝ W]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p → Λ p = M (VectorPolynomial.siteEvaluation
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      ∃ w : W, Λ ((map (Int.castRingHom ℝ) (∏ i, rowPolynomial (rows i))) ⊗ₜ[ℝ] w) ≠ 0 := by
  obtain ⟨selection, hdet⟩ := integer_difference_exists_pivot difference hlin
  simpa only [Fintype.card_fin] using exists_integer_site_directions
    root difference selection hdet hH hD hroot hdiff Λ h hnonfactor

end Erdos3.BooleanCubeKernel

end

end OAI
