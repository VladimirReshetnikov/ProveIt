import OAI.Combinatorics.Progressions.Lattices.IndependentIntegerSiteDirections

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_ambient_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ)
    (hbound : VectorPolynomial.MonomialRowBound Λ h C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        Λ (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |VectorPolynomial.contractedRow Λ (map (Int.castRingHom ℝ) (∏ i, P i)) j| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, VectorPolynomial.contractedRow Λ
        (map (Int.castRingHom ℝ) (∏ i, P i)) j * w.val j) ≠ 0 := by
  obtain ⟨selection, hdet⟩ := integer_difference_exists_pivot difference hlin
  obtain ⟨forms, hlen, hforms, hz, w, hw⟩ := exists_integral_vector_mode_witness
    root difference selection hdet hH hD hroot hdiff
    (Λ.comp (VectorPolynomial.map W.subtype)) h hnonfactor
  simp only [Fintype.card_fin] at hforms
  subst h
  let P : Fin forms.length → MvPolynomial (Option K) ℤ := forms.get
  have hmem (i : Fin forms.length) : P i ∈ forms := List.get_mem _ _
  have hprod : (∏ i, P i) = forms.prod := by
    rw [← Fin.prod_ofFn, List.ofFn_get]
  refine ⟨P, (fun i => hforms _ (hmem i)), ?_, ?_, w, ?_⟩
  · intro s
    exact List.exists_mem_iff_get.mp (hz s)
  · intro j
    rw [map_prod]
    exact VectorPolynomial.contractedRow_prod_bound Λ
      (fun i => map (Int.castRingHom ℝ) (P i))
      (fun i => (hforms _ (hmem i)).1.map _) (fun i => (hforms _ (hmem i)).2) hC hbound j
  · rw [VectorPolynomial.contractedRow_apply, hprod]
    exact hw

end Erdos3.BooleanCubeKernel

end

end OAI
