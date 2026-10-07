import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ stride cells center)

theorem path_base_abs_le (z : A.Path) (x : X) : |(z.1.val x : ℝ)| ≤ N x := by
  have hz := z.1.property
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
  have hax := (mem_integerBox _ _).mp ha x
  have hx := congrFun he x
  simp only [Pi.add_apply] at hx
  have hi : |z.1.val x| ≤ (N x : ℤ) := by
    rw [abs_of_nonneg (by omega : 0 ≤ z.1.val x)]
    omega
  exact_mod_cast hi

theorem path_spatial_center_mass_le_trim (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤
      1 + τ / 4 := by
  have hN : (0 : ℝ) < N x := by exact_mod_cast A.size_pos x
  have hnoise := rectangularWeightIndices_zero_bound
    (allocatedExternalCandidateWidths B U b S N τ ξ) z.2.property (none, x)
  have hnoise' : |(z.2.val (none, x) : ℝ)| ≤ τ * (N x : ℝ) / 8 := by
    simpa only [allocatedExternalCandidateWidths, narrowTrimmedSpatialWidths,
      trimmedSpatialWidths, centeredSpatialWidths, one_mul, mul_div_assoc] using hnoise
  have hcenter : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| ≤
      (N x : ℝ) + τ * (N x : ℝ) / 8 := by
    simp only [jointIntegerFrame, Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (A.path_base_abs_le z x) hnoise')
  have hnorm : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) ≤
      1 + τ / 8 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  linarith

theorem path_spatial_center_mass_le (hτ1 : τ ≤ 1) (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ 2 := by
  have h := A.path_spatial_center_mass_le_trim z x
  linarith

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
