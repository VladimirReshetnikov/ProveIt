import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module MeasureTheory

theorem exists_integral_subspace_basis {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ))
    (hspan : Submodule.span ℝ {x : U | ∀ a, ∃ n : ℤ, x.val a = n} = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ U)) ℝ U,
      ∀ i a, ∃ n : ℤ, (b i).val a = n := by
  classical
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ {x : U | ∀ a, ∃ n : ℤ, x.val a = n}
  rw [hspan, finrank_top] at hex
  obtain ⟨v, hv, hs, hi⟩ := hex
  refine ⟨Basis.mk hi (by rw [hs]), ?_⟩
  intro i a
  simpa only [Basis.mk_apply] using hv i a

theorem exists_coefficient_torus_haar {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (hspan : ∀ j, Submodule.span ℝ {x : U j | ∀ a, ∃ n : ℤ, x.val a = n} = ⊤) :
    ∃ μ : Measure (CoefficientTorus (K := K) U), IsProbabilityMeasure μ ∧ μ.IsAddLeftInvariant := by
  choose b hb using fun j => exists_integral_subspace_basis (U j) (hspan j)
  exact ⟨coefficientTorusHaar U b hb, inferInstance, inferInstance⟩

end Erdos3.VectorPolynomial

end

end OAI
