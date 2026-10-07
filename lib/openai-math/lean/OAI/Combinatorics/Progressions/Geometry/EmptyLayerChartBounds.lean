import OAI.Combinatorics.Progressions.Linear.NormalizedBasisBounds
import OAI.Combinatorics.Progressions.Linear.OrthogonalBasisChart
import OAI.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def normalizedOrthogonalChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := orthogonalBasisChart W (normalizedAxisBasis b)

theorem normalizedOrthogonalChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    normalizedOrthogonalChart W b x = (W.orthogonalProjectionOnto x,
      fun i => b.equivFun (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ)) := by
  rw [normalizedOrthogonalChart, orthogonalBasisChart_apply]
  refine Prod.ext rfl ?_
  funext i
  exact normalizedAxisBasis_coordinates b _ i

theorem normalizedOrthogonalChart_integer_coordinates (W : Submodule ℝ E)
    (b : Basis (Fin n) ℝ Wᗮ) (x : E)
    (hx : Wᗮ.orthogonalProjectionOnto x ∈ span ℤ (Set.range b)) :
    ∃ z : Fin n → ℤ, ∀ i,
      (normalizedOrthogonalChart W b x).2 i = (z i : ℝ) / (basisAxisScale b i : ℝ) := by
  have h := (b.mem_span_iff_repr_mem ℤ _).mp hx
  choose z hz using h
  refine ⟨z, ?_⟩
  intro i
  rw [normalizedOrthogonalChart_apply]
  change b.repr (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ) = _
  rw [← hz i]
  simp

variable [MeasurableSpace E] [BorelSpace E]

theorem normalizedOrthogonalChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis (Fin n) ℝ Wᗮ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖normalizedOrthogonalChart W b x‖ ≤
      (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  apply orthogonalBasisChart_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_coordinates_bound o b hB hD hb hprod

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizedOrthogonalChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖b i‖ ≤ B) (p : W × (Fin n → ℝ)) :
    ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖ := by
  apply orthogonalBasisChart_symm_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_synthesis_bound b hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {D : Type*} [Fintype D] [IsEmpty D] {n : ℕ}

theorem normalizedOrthogonalChart_norm_le_zero_of_isEmpty
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (x : EuclideanSpace ℝ D) :
    ‖normalizedOrthogonalChart W b x‖ ≤ 0 * ‖x‖ := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

theorem normalizedOrthogonalChart_symm_norm_le_zero_of_isEmpty
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (x : W × (Fin n → ℝ)) :
    ‖(normalizedOrthogonalChart W b).symm x‖ ≤ 0 * ‖x‖ := by
  have hx : (normalizedOrthogonalChart W b).symm x = 0 := Subsingleton.elim _ _
  simp [hx]

theorem hasLayerSamplingRank_of_isEmpty {I J : Type*} [Fintype J] [IsEmpty J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) : HasLayerSamplingRank h T R W p := by
  intro a ha hw
  obtain ⟨w, hw⟩ := hw
  simp at hw

theorem VectorPolynomial.degreeLE_of_subsingleton
    {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Subsingleton V]
    (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) : DegreeLE w d p := by
  intro α hα
  exact Subsingleton.elim _ _

end Erdos3

end

end OAI
