import OAI.Combinatorics.Progressions.Geometry.AllocatedRecoveredNormalizedTopChart
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
import OAI.Combinatorics.Progressions.Linear.SpatialFrameSlopeBudget
import OAI.Combinatorics.Progressions.Polynomial.NormalizedFrozenPolynomialMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {K X : Type*} [Fintype K]

theorem jointIntegerFullChart_normalized_spatial_top
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ) (x : X) :
    aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart (jointIntegerFullChart J a v tag) i))
      (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)) =
      C ((N x : ℝ)⁻¹) * homogeneousComponent 1
        (affineFramePolynomial (fun k z => (jointIntegerFrame (a, v) k z : ℝ)) x) := by
  simp only [normalizedRealPolynomialChart_inl, map_mul, aeval_C, aeval_X]
  change C ((N x : ℝ)⁻¹) * homogeneousComponent 1
    (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)) = _
  rw [affineFramePolynomial_map]
  rfl

variable {G : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem layerSamplerBox_sum_le_zero_root_budget :
    (∑ k, layerSamplerBox B U b S k) ≤
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => layerSamplerBox_le B U b S k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

theorem allocatedRecoveredIntegerFullChart_spatial_top_mass [Fintype X]
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)))) ≤ τ / 8 := by
  unfold allocatedRecoveredIntegerFullChart
  rw [jointIntegerFullChart_normalized_spatial_top]
  have hT : ∀ k, 0 ≤ layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k)
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN x
  have hsum := narrowSpatial_frame_slope_sum
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hξ N hN
    (layerSamplerBox B U b S) hT (layerSamplerBox_sum_le_zero_root_budget B U b S) v hv x
  refine (spatialAffineTop_scaled_inv_mul_mass_le
    (fun k z => (jointIntegerFrame (a, v) k z : ℝ))
    (layerSamplerBox B U b S) hT x (N x) hn).trans ?_
  change (N x : ℝ)⁻¹ * (∑ k, |(v (some k, x) : ℝ)| * layerSamplerBox B U b S k) ≤ _
  calc
    _ ≤ (N x : ℝ)⁻¹ * (τ * (N x : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = τ / 8 := by field_simp

theorem allocatedFrozenIntegerFullChart_spatial_top_mass [Fintype X]
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬ keep i} → ℤ)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
        (integerSampledRealChart
          (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)))) ≤ τ / 8 := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) < 1).trans_le (layerSamplerBox_one_le B U b S k)
  let P := integerSampledRealChart
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x)
  have hdegree : P.totalDegree ≤ 1 :=
    (mem_weightedSupportLE_one_iff _ _).mp
      (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample (Sum.inl x))
  have hbound := allocatedRecoveredIntegerFullChart_spatial_top_mass
    B U b S o poly hm c a N hN hτ hξ v hv sample x
  simp only [normalizedRealPolynomialChart_inl, map_mul, aeval_C, aeval_X] at hbound ⊢
  change realPolynomialMass (scaleMvPolynomialAxes
    (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
    (C ((N x : ℝ)⁻¹) * homogeneousComponent 1
      (integerSampledRealChart (fun z => freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) (Sum.inl x)))) ≤ _
  rw [integerSampledRealChart_freeze]
  change realPolynomialMass (scaleMvPolynomialAxes
    (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
    (C ((N x : ℝ)⁻¹) * homogeneousComponent 1
      (freezePolynomial keep (fun i => (fixed i : ℝ)) P))) ≤ _
  rw [freezePolynomial_top keep _ hdegree]
  have he : C ((N x : ℝ)⁻¹) * freezePolynomial keep 0 (homogeneousComponent 1 P) =
      freezePolynomial keep 0 (C ((N x : ℝ)⁻¹) * homogeneousComponent 1 P) := by
    simp only [map_mul, freezePolynomial, aeval_C]
    rfl
  rw [he]
  exact (normalizedMass_freezePolynomial_le keep (layerSamplerBox B U b S) hT 0
    (fun i => by simpa only [Pi.zero_apply, abs_zero] using (hT i.val).le) _).trans hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag_mass
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  rw [h.integerFullChart_normalized_top_tag B U b hb o S hR hσ poly hm hp c a v sample read N j i]
  exact (normalizedMass_neg_weightedHomogeneousComponent_le _ _ _ _).trans
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 i)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  cases i with
  | inl x =>
    apply (allocatedRecoveredIntegerFullChart_spatial_top_mass B U b S o poly hm c a
      N hN hτ hξ v hv sample x).trans
    have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hone := mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    apply (show τ / 8 ≤ 1 by linarith).trans
    simpa only [one_mul] using hone
  | inr z =>
    exact h.integerFullChart_normalized_top_tag_mass B U b hb o S hR hσ poly hm hp c a v
      sample read hσ1 C hC hchart hsmall (fun x => (N x : ℝ)) z.1 z.2

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  change realPolynomialMass (scaleMvPolynomialAxes _
    (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)))) _)) ≤ _
  rw [aeval_frozen_integer_top (fullTaggedVariableWeight J)
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  exact (normalizedMass_freezePolynomial_le keep _ hT 0
    (fun i => by simpa only [Pi.zero_apply, abs_zero] using (hT i.val).le) _).trans
    (h.integerFullChart_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall i)

end Erdos3.VectorPolynomial

end

end OAI
