import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
import OAI.Combinatorics.Progressions.Geometry.ActualCandidateSpatialCenter
import OAI.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
import OAI.Combinatorics.Progressions.Polynomial.FullTaggedProjectionPolynomial
import OAI.Combinatorics.Progressions.Probability.FullFrozenChartMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedRealMatrixProjection_single
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) (a i : J j) :
    fullTaggedRealMatrixProjection J P j (Pi.single a 1) i = (P j i a : ℝ) :=
  congrFun (Matrix.mulVec_single_one (Matrix.of fun s t => (P j s t : ℝ)) a) i

theorem fullTaggedRealMatrixProjection_rowSum_le
    (P : ∀ j, Matrix (J j) (J j) ℚ) {B : ℝ}
    (hP : ∀ j i a, rationalLogHeight (P j i a) ≤ B) (j : Fin m) (i : J j) :
    (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) ≤
      (Fintype.card (J j) : ℝ) * Real.exp B := by
  calc
    _ ≤ ∑ _a : J j, Real.exp B := by
      apply Finset.sum_le_sum
      intro a _
      rw [fullTaggedRealMatrixProjection_single]
      exact (rational_abs_real_le_numerator (P j i a)).trans
        ((rationalLogHeight_le_iff _ _).mp (hP j i a)).1
    _ = _ := by simp

theorem fullTaggedRealMatrixProjection_slow_mass_row_le
    (P : ∀ j, Matrix (J j) (J j) ℚ) {B d : ℝ}
    (hP : ∀ j i a, rationalLogHeight (P j i a) ≤ B)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d) (nVars : ℕ)
    (j : Fin m) (i : J j) :
    (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) *
      (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) ≤
      d * Real.exp B * (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) := by
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (fullTaggedRealMatrixProjection_rowSum_le J P hP j i).trans
    (mul_le_mul_of_nonneg_right (hdim j) (Real.exp_nonneg B))

theorem fullTaggedRealMatrixProjection_slow_mass_row_le_exp
    (P : ∀ j, Matrix (J j) (J j) ℚ) {B d L : ℝ}
    (hP : ∀ j i a, rationalLogHeight (P j i a) ≤ B)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d) (nVars : ℕ)
    (hVars : ((nVars + 1 : ℕ) : ℝ) ≤ Real.exp L)
    (j : Fin m) (i : J j) :
    (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) *
      (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) ≤
      Real.exp (B + d + (m : ℝ) + (m : ℝ) * L) := by
  have hrow : (∑ a : J j, |fullTaggedRealMatrixProjection J P j (Pi.single a 1) i|) ≤
      Real.exp d * Real.exp B :=
    (fullTaggedRealMatrixProjection_rowSum_le J P hP j i).trans
      (mul_le_mul_of_nonneg_right
        ((hdim j).trans (by linarith [Real.add_one_le_exp d])) (Real.exp_nonneg B))
  have hm : ((m + 1 : ℕ) : ℝ) ≤ Real.exp (m : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (m : ℝ)
  have hv : (((nVars + 1 : ℕ) : ℝ) ^ m) ≤ Real.exp ((m : ℝ) * L) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hVars m
  calc
    _ ≤ (Real.exp d * Real.exp B) * (Real.exp (m : ℝ) * Real.exp ((m : ℝ) * L)) :=
      mul_le_mul hrow (mul_le_mul hm hv (by positivity) (Real.exp_nonneg _))
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedCenteredCoordinates
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (a : Σ j, J j) : MvPolynomial X ℝ :=
  coordinate (LinearMap.proj a.2 : (J a.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly a.1) -
    C (c a.1 a.2)

noncomputable def fullTaggedSlowProjectionChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (z : X ⊕ (Σ j, J j)) : MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  aeval (fullTaggedLinearMapChart J P)
    (normalizedRealPolynomialChart N (fullTaggedCenteredCoordinates J poly c) z)

@[simp] theorem fullTaggedSlowProjectionChart_inl
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) (x : X) :
    fullTaggedSlowProjectionChart J P N poly c (Sum.inl x) =
      C ((N x)⁻¹) * MvPolynomial.X (Sum.inl x) := by
  simp [fullTaggedSlowProjectionChart, fullTaggedLinearMapChart]

@[simp] theorem fullTaggedSlowProjectionChart_inr
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (j : Fin m) (i : J j) :
    fullTaggedSlowProjectionChart J P N poly c (Sum.inr ⟨j, i⟩) =
      fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩) -
        rename Sum.inl (fullTaggedCenteredCoordinates J poly c ⟨j, i⟩) := by
  rw [fullTaggedSlowProjectionChart, normalizedRealPolynomialChart_inr,
    map_sub, aeval_X, aeval_rename, rename_eq_aeval]
  rfl

omit [∀ j, Fintype (J j)] in
theorem fullTaggedCenteredCoordinates_support
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, J j → ℝ) (a : Σ j, J j) :
    fullTaggedCenteredCoordinates J poly c a ∈
      weightedSupportLE (fun _ : X => 1) (a.1.val + 1) := by
  apply (weightedSupportLE _ _).sub_mem ?_ (weightedSupportLE_C _ _ _)
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  apply (scalar_weightedDegree_le_iff _ _ _).mpr
  intro α hα
  rw [coeff_coordinate, hp a.1 α hα, map_zero]

omit [∀ j, Fintype (J j)] in
theorem fullTaggedCenteredCoordinates_top
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (a : Σ j, J j) :
    homogeneousComponent (a.1.val + 1) (fullTaggedCenteredCoordinates J poly c a) =
      fullTaggedMajorTopCoordinates J poly a := by
  have hc : homogeneousComponent (a.1.val + 1) (C (c a.1 a.2) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simp
  simp only [fullTaggedCenteredCoordinates, map_sub, hc, sub_zero,
    fullTaggedMajorTopCoordinates]

theorem fullTaggedSlowProjectionChart_support
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, J j → ℝ) (z : X ⊕ (Σ j, J j)) :
    fullTaggedSlowProjectionChart J P N poly c z ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J z) := by
  cases z with
  | inl x =>
    rw [fullTaggedSlowProjectionChart_inl, ← smul_eq_C_mul]
    exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ _)
  | inr a =>
    rw [fullTaggedSlowProjectionChart_inr]
    apply (weightedSupportLE _ _).sub_mem
    · intro α hα
      exact (fullTaggedLinearMapChart_homogeneous J P (Sum.inr a) (mem_support_iff.mp hα)).le
    · exact majorParameterRename_degree (fun _ : X => 1) (fun a : Σ j, J j => a.1.val + 1)
        (fullTaggedCenteredCoordinates_support J poly hp c a)

theorem fullTaggedSlowProjectionChart_top
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (z : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J z)
        (fullTaggedSlowProjectionChart J P N poly c z) =
      aeval (fullTaggedLinearMapChart J P)
        (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) z) := by
  rw [fullTaggedSlowProjectionChart, ← aeval_weightedHomogeneousComponent
    (fullTaggedVariableWeight J) (fullTaggedVariableWeight J) _
    (fullTaggedLinearMapChart_homogeneous J P)]
  congr 1
  cases z with
  | inl x =>
    exact weightedHomogeneousComponent_eq_self
      ((isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x)).C_mul _)
  | inr a =>
    rw [normalizedRealPolynomialChart_inr, normalizedRealPolynomialChart_inr, map_sub,
      weightedHomogeneousComponent_eq_self
        (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr a))]
    congr 1
    rw [rename_eq_aeval, ← aeval_weightedHomogeneousComponent (fun _ : X => 1)
      (fullTaggedVariableWeight J) (MvPolynomial.X ∘ Sum.inl)
      (fun x => isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x))]
    rw [← rename_eq_aeval]
    exact congrArg (rename Sum.inl) (fullTaggedCenteredCoordinates_top J poly c a)

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

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

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    aeval (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inl x)) =
      C ((N x)⁻¹) *
        affineFramePolynomial (fun k z => (jointIntegerFrame (a, v) k z : ℝ)) x := by
  rw [fullTaggedSlowProjectionChart_inl, map_mul, aeval_C, aeval_X]
  change C ((N x)⁻¹) * MvPolynomial.map (Int.castRingHom ℝ)
    (affineFramePolynomial (jointIntegerFrame (a, v)) x) = _
  rw [affineFramePolynomial_map]
  rfl

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x) (N : X → ℝ)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) (i : J j) :
    aeval (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)) =
      -(∑ k : J j, P j (Pi.single k 1) i •
        mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) k) := by
  rw [fullTaggedSlowProjectionChart_inr, map_sub, aeval_rename]
  simp only [fullTaggedLinearMapChart, map_sum, map_smul, aeval_X]
  exact sum_projection_remainder_eq (P j) (U j) (hP j) (poly j) (hm j)
    (c j).val (c j).property _ _ _
    (fun k => h.integerFullChart_polynomial_remainder B U b hb o S hR hσ poly hm
      hp c a v sample read j k) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

theorem normalizedMass_neg_linearCombination_le {K I : Type*} [Fintype I]
    (T : K → ℝ) (a : I → ℝ) (p : I → MvPolynomial K ℝ) {M : ℝ}
    (hp : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (p i)) ≤ M) :
    realPolynomialMass (scaleMvPolynomialAxes T (-(∑ i, a i • p i))) ≤
      (∑ i, |a i|) * M := by
  simp only [scaleMvPolynomialAxes_eq_aeval, map_neg, map_sum, map_smul,
    normalizedPolynomialMass_neg]
  apply (realPolynomialMass_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [realPolynomialMass_smul]
  simpa only [scaleMvPolynomialAxes_eq_aeval] using
    mul_le_mul_of_nonneg_left (hp i) (abs_nonneg (a i))

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

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

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (hN : ∀ x, 0 < N x) (T : LayerSamplerVariables G I n B → ℝ)
    (hT : ∀ k, 0 ≤ T k)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inl x)))) ≤
      |(jointIntegerFrame (a, v) none x : ℝ)| / N x +
        (N x)⁻¹ * ∑ k, |(jointIntegerFrame (a, v) (some k) x : ℝ)| * T k := by
  rw [allocatedRecoveredIntegerFullChart_slowProjection_spatial]
  exact spatialAffineFull_scaled_inv_mul_mass_le _ T hT x (N x) (hN x)

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass_of_support
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) (Sum.inl x)))) ≤
      |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 := by
  have hT : ∀ k, 0 ≤ layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k)
  have hn : ∀ x, (0 : ℝ) < N x := fun x => by exact_mod_cast hN x
  apply (allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass B U b o poly hm P
    (fun x => (N x : ℝ)) hn (layerSamplerBox B U b S) hT c a v sample x).trans
  apply add_le_add le_rfl
  have hsum := narrowSpatial_frame_slope_sum
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hξ N hN
    (layerSamplerBox B U b S) hT (layerSamplerBox_sum_le_zero_root_budget B U b S) v hv x
  change (N x : ℝ)⁻¹ * (∑ k, |(v (some k, x) : ℝ)| * layerSamplerBox B U b S k) ≤ _
  calc
    _ ≤ (N x : ℝ)⁻¹ * (τ * (N x : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (hn x).le)
    _ = τ / 8 := by field_simp [(hn x).ne']

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_tag_mass
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x) (N : X → ℝ)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)))) ≤
      (∑ k : J j, |P j (Pi.single k 1) i|) *
        (((m + 1 : ℕ) : ℝ) *
          ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) := by
  rw [h.integerFullChart_slowProjection_tag B U b hb o S hR hσ poly hm P hP N
    hp c a v sample read j i]
  apply normalizedMass_neg_linearCombination_le
  intro k
  exact allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
    hsmall j (sample j) (h.2.2.1 j).2 k

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_mass
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
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
    (M : ℝ)
    (hcenter : ∀ x, |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ M)
    (hrows : ∀ j i, (∑ k : J j, |P j (Pi.single k 1) i|) *
      (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ≤ M)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) z))) ≤ M := by
  cases z with
  | inl x =>
    exact (allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass_of_support B U b o S
      poly hm P N hN hτ hξ c a v hv sample x).trans (hcenter x)
  | inr z =>
    exact (h.integerFullChart_slowProjection_tag_mass B U b hb o S hR hσ poly hm P hP
      (fun x => (N x : ℝ)) hp c a v sample read hσ1 C hC hchart hsmall z.1 z.2).trans
      (hrows z.1 z.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

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

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_slowProjection_mass
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
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
    (M : ℝ)
    (hcenter : ∀ x, |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ M)
    (hrows : ∀ j i, (∑ k : J j, |P j (Pi.single k 1) i|) *
      (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) z))) ≤ M := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  apply (normalizedMass_aeval_frozen_integer_chart_le
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep
    (layerSamplerBox B U b S) hT fixed hfixed _).trans
  exact h.integerFullChart_slowProjection_mass B U b hb o S hR hσ poly hm P hP N hN
    hτ hξ hp c a v hv sample read hσ1 C hC hchart hsmall M hcenter hrows z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedSlowProjectionChart_physical_spatial
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) (a : X) :
    MvPolynomial.eval (fun z => (fullTaggedPhysicalIntegerPoint J poly c x z : ℝ))
      (fullTaggedSlowProjectionChart J P (fun z => (N z : ℝ)) poly c (Sum.inl a)) =
      (N a : ℝ)⁻¹ * (x a : ℝ) := by
  simp [fullTaggedPhysicalIntegerPoint]

theorem fullTaggedSlowProjectionChart_physical_spatial_abs_le_one [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) (hx : x ∈ integerBox N) (a : X) :
    |MvPolynomial.eval (fun z => (fullTaggedPhysicalIntegerPoint J poly c x z : ℝ))
      (fullTaggedSlowProjectionChart J P (fun z => (N z : ℝ)) poly c (Sum.inl a))| ≤ 1 := by
  rw [fullTaggedSlowProjectionChart_physical_spatial]
  have ha := (mem_integerBox N x).mp hx a
  have hx0 : (0 : ℝ) ≤ x a := by exact_mod_cast ha.1
  have hxN : (x a : ℝ) < N a := by exact_mod_cast ha.2
  have hN : (0 : ℝ) < N a := lt_of_le_of_lt hx0 hxN
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hN.le) hx0), mul_comm, ← div_eq_mul_inv]
  exact (div_le_one hN).mpr hxN.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

omit [∀ j, Fintype (J j)] in

theorem fullTaggedCenteredCoordinates_eval
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedCenteredCoordinates J poly c ⟨j, i⟩) =
      eval x (poly j) i - c j i := by
  have he : eval₂ x (poly j) = eval x (poly j) := by
    simpa using eval₂_algebraMap (S := ℝ) x (poly j)
  rw [fullTaggedCenteredCoordinates, map_sub, eval_C, ← coordinate_eval₂, he]
  rfl

theorem fullTaggedSlowProjectionChart_physical_tag
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (j : Fin m) (i : J j) :
    MvPolynomial.eval
      (fun z => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x z : ℝ))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)) =
      P j (fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ) -
        (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a)) i := by
  have hmem : eval (fun z => (x z : ℝ)) (poly j) - (c j).val ∈ U j :=
    (U j).sub_mem ((eval_mem_iff_coefficients (U j) (poly j)).mpr (hm j) _) (c j).property
  rw [fullTaggedSlowProjectionChart_inr, map_sub, fullTaggedLinearMapChart_eval_tag,
    MvPolynomial.eval_rename]
  change P j (fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ)) i -
    MvPolynomial.eval (fun z => (x z : ℝ))
      (fullTaggedCenteredCoordinates J poly (fun j => (c j).val) ⟨j, i⟩) = _
  rw [fullTaggedCenteredCoordinates_eval]
  change _ = P j ((fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ)) -
    (eval (fun z => (x z : ℝ)) (poly j) - (c j).val)) i
  rw [map_sub, hP j _ hmem, Pi.sub_apply, Pi.sub_apply]

theorem fullTaggedSlowProjectionChart_physical_tag_abs_le
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (j : Fin m) (i : J j) :
    |MvPolynomial.eval
      (fun z => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x z : ℝ))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩))| ≤
      ∑ a : J j, |P j (Pi.single a 1) i| := by
  rw [fullTaggedSlowProjectionChart_physical_tag J U P hP N poly hm c x j i,
    linearMap_pi_apply_eq_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [abs_sub_comm]
  exact (abs_sub_round _).trans (by norm_num)

theorem fullTaggedSlowProjectionChart_physical_abs_le [Fintype X]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (hx : x ∈ integerBox N) {M : ℝ}
    (hrows : ∀ j i, (∑ a : J j, |P j (Pi.single a 1) i|) ≤ M)
    (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval
      (fun v => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x v : ℝ))
      (fullTaggedSlowProjectionChart J P (fun v => (N v : ℝ)) poly (fun j => (c j).val) z)| ≤
      max 1 M := by
  cases z with
  | inl a =>
    exact (fullTaggedSlowProjectionChart_physical_spatial_abs_le_one
      J P N poly (fun j => (c j).val) x hx a).trans (le_max_left _ _)
  | inr a =>
    exact (fullTaggedSlowProjectionChart_physical_tag_abs_le
      J U P hP (fun v => (N v : ℝ)) poly hm c x a.1 a.2).trans
        ((hrows a.1 a.2).trans (le_max_right _ _))

theorem fullTaggedSlowProjectionChart_physical_abs_le_rational [Fintype X]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (Q : ∀ j, Matrix (J j) (J j) ℚ)
    (hQ : ∀ j y, y ∈ U j → fullTaggedRealMatrixProjection J Q j y = y)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (hx : x ∈ integerBox N) {H d : ℝ}
    (hheight : ∀ j i a, rationalLogHeight (Q j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval
      (fun v => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x v : ℝ))
      (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J Q)
        (fun v => (N v : ℝ)) poly (fun j => (c j).val) z)| ≤ max 1 (d * Real.exp H) := by
  apply fullTaggedSlowProjectionChart_physical_abs_le J U
    (fullTaggedRealMatrixProjection J Q) hQ N poly hm c x hx _ z
  intro j i
  exact (fullTaggedRealMatrixProjection_rowSum_le J Q hheight j i).trans
    (mul_le_mul_of_nonneg_right (hdim j) (Real.exp_nonneg H))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def actualCandidateSlowProjectionMassBudget (m nVars : ℕ) (d H : ℝ) : ℝ :=
  2 + d * Real.exp H * (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m)

theorem actualCandidateSlowProjectionMassBudget_two_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) : 2 ≤ actualCandidateSlowProjectionMassBudget m nVars d H := by
  unfold actualCandidateSlowProjectionMassBudget
  exact le_add_of_nonneg_right (by positivity)

theorem actualCandidateSlowProjectionMassBudget_one_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) : 1 ≤ actualCandidateSlowProjectionMassBudget m nVars d H :=
  (by norm_num : (1 : ℝ) ≤ 2).trans
    (actualCandidateSlowProjectionMassBudget_two_le m nVars hd)

theorem actualCandidateSlowProjectionMassBudget_max_le (m nVars : ℕ) {d H : ℝ}
    (hd : 0 ≤ d) :
    max 1 (d * Real.exp H) ≤ actualCandidateSlowProjectionMassBudget m nVars d H := by
  apply max_le (actualCandidateSlowProjectionMassBudget_one_le m nVars hd)
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hn : (1 : ℝ) ≤ ((nVars + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos nVars
  have hfactor : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m := by
    simpa only [one_mul] using mul_le_mul hm (one_le_pow₀ hn) (by norm_num) (by positivity)
  have h := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hd (Real.exp_nonneg H))
  unfold actualCandidateSlowProjectionMassBudget
  rw [mul_one] at h
  linarith

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem slowProjection_mass
    (P : ∀ j, Matrix (J j) (J j) ℚ)
    (hP : ∀ j x, x ∈ U j → fullTaggedRealMatrixProjection J P j x = x)
    {d H : ℝ} (hd : 0 ≤ d)
    (hheight : ∀ j i a, rationalLogHeight (P j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes
      (fun i : C.Variables => layerSamplerBox B U b S i.val)
      (aeval (integerSampledRealChart C.integerChart)
        (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J P)
          (fun x => (N x : ℝ)) poly (fun j => (C.centerLift j).val) z))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) d H := by
  have hv : C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  apply C.recovered.integerFullChart_frozen_slowProjection_mass B U b hb o S hR hσ poly hm
    (fullTaggedRealMatrixProjection J P) hP N A.size_pos A.trim_pos hξ1 hp
    C.centerLift C.path.1.val C.path.2.val hv C.sample C.read hσ1 Cgeo hCgeo hchart hsmall
    (actualCandidateSlowProjectionMassBudget m
      (Fintype.card (LayerSamplerVariables G I n B)) d H) ?_ ?_
    C.keep C.fixed C.fixed_abs_le_box z
  · intro x
    exact (A.path_spatial_center_mass_le hτ1 C.path x).trans
      (actualCandidateSlowProjectionMassBudget_two_le _ _ hd)
  · intro j i
    have hrow := fullTaggedRealMatrixProjection_slow_mass_row_le J P hheight hdim
      (Fintype.card (LayerSamplerVariables G I n B)) j i
    unfold actualCandidateSlowProjectionMassBudget
    linarith

theorem slowProjection_mass_sides
    (P : ∀ j, Matrix (J j) (J j) ℚ)
    (hP : ∀ j x, x ∈ U j → fullTaggedRealMatrixProjection J P j x = x)
    {d H : ℝ} (hd : 0 ≤ d)
    (hheight : ∀ j i a, rationalLogHeight (P j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : C.Variables => (A.sides i.val : ℝ))
      (aeval (integerSampledRealChart C.integerChart)
        (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J P)
          (fun x => (N x : ℝ)) poly (fun j => (C.centerLift j).val) z))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) d H := by
  have hT : (fun i : C.Variables => (A.sides i.val : ℝ)) =
      (fun i : C.Variables => layerSamplerBox B U b S i.val) := by
    funext i
    exact (allocatedParameterBox_side_eq B U b S i.val).symm
  rw [hT]
  exact C.slowProjection_mass P hP hd hheight hdim hτ1 hξ1 hp hσ1 Cgeo hCgeo hchart hsmall z

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
