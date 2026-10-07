import OAI.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualArray {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.id - (constantCoefficientArray U).comp (coefficientEvaluationArray U t)

theorem coefficientResidualArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientResidualArray U t x ∈ coefficientIntegerLattice U :=
  (coefficientIntegerLattice U).sub_mem hx (constantCoefficientArray_preserves_lattice U _
    (coefficientEvaluationArray_preserves_lattice U t x hx))

theorem coefficientResidualArray_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientEvaluationArray U t (coefficientResidualArray U t x) = 0 := by
  simp only [coefficientResidualArray, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, coefficientEvaluationArray_constant, sub_self]

theorem coefficientResidualArray_factor_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (L : CoefficientArray (K := K) U →ₗ[ℝ] ℝ) :
    L.comp (coefficientResidualArray U t) = 0 ↔
      ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ, L = M.comp (coefficientEvaluationArray U t) := by
  constructor
  · intro h
    refine ⟨L.comp (constantCoefficientArray U), ?_⟩
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun h x
    simpa only [LinearMap.comp_apply, coefficientResidualArray, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, LinearMap.zero_apply, sub_eq_zero] using hx
  · rintro ⟨M, rfl⟩
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, coefficientResidualArray_evaluation, map_zero,
      LinearMap.zero_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientArray_factor_to_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (s₀ : S) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ)
    (hM : coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t))
    (j : Fin m) :
    ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p) := by
  let A : (S → U j) →ₗ[ℝ] (BoundedCoefficientExponent Empty (j.val + 1) → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj s₀)
  let Mj := M.comp ((coefficientLayerInsertion U j).comp A)
  refine ⟨Mj, ?_⟩
  intro p hp
  let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => coefficients p d.val
  have hv : boundedArrayPolynomial (j.val + 1) v = p := boundedArrayPolynomial_reconstruct p hp
  have he := DFunLike.congr_fun hM (coefficientLayerInsertion U j v)
  rw [LinearMap.comp_apply, coefficientArrayFunctional_layerInsertion,
    coefficientEvaluationArray_layerInsertion] at he
  rw [← hv, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
  exact he

theorem coefficientArray_factor_of_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : ∀ j, ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p)) :
    ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ,
      coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t) := by
  choose Mj hMj using hf
  let A (j : Fin m) : CoefficientArray (K := Empty) U →ₗ[ℝ] (S → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj (⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ :
      CoefficientSlot Empty m))
  let M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ := ∑ j, (Mj j).comp (A j)
  refine ⟨M, ?_⟩
  apply LinearMap.ext
  intro x
  have hj (j : Fin m) :
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) =
        Mj j (A j (coefficientEvaluationArray U t x)) := by
    let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => x ⟨j, d⟩
    have he := hMj j (boundedArrayPolynomial (j.val + 1) v)
      (boundedArrayPolynomial_degreeLE (j.val + 1) v)
    rw [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he
    exact he
  calc
    _ = ∑ j : Fin m, subspaceArrayFunctional (U j)
        (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) := by
      change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ j, Mj j (A j (coefficientEvaluationArray U t x)) := Finset.sum_congr rfl (fun j _ => hj j)
    _ = _ := by simp only [M, LinearMap.comp_apply, LinearMap.sum_apply]

end Erdos3.VectorPolynomial

end

end OAI
