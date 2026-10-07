import OAI.Combinatorics.Progressions.Estimates.HomogeneousComponentTopSubstitution
import OAI.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
import OAI.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem aeval_frozen_integer_top {σ K : Type*}
    (w : σ → ℕ) (β : σ → MvPolynomial K ℤ)
    (hβ : ∀ z, MvPolynomial.map (Int.castRingHom ℝ) (β z) ∈
      weightedSupportLE (fun _ => 1) (w z))
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (fun z => homogeneousComponent (w z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β z)))) p =
      freezePolynomial keep (0 : {i // ¬keep i} → ℝ)
        (aeval (fun z => homogeneousComponent (w z)
          (MvPolynomial.map (Int.castRingHom ℝ) (β z))) p) := by
  simp_rw [freezePolynomial_map, freezePolynomial_top keep _
    ((mem_weightedSupportLE_one_iff _ _).mp (hβ _))]
  exact (MvPolynomial.comp_aeval_apply _ (freezePolynomial keep 0) p).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem normalizedRealPolynomialChart_top_inr
    {X Tags K : Type*} (weight : Tags → ℕ) (N : X → ℝ)
    (poly : Tags → MvPolynomial X ℝ)
    (hp : ∀ i, poly i ∈ weightedSupportLE (fun _ : X => 1) (weight i))
    (β : X ⊕ Tags → MvPolynomial K ℝ)
    (hβ : ∀ z, β z ∈ weightedSupportLE (fun _ : K => 1)
      (Sum.elim (fun _ : X => 1) weight z)) (i : Tags) :
    aeval (fun z => homogeneousComponent (Sum.elim (fun _ : X => 1) weight z) (β z))
        (normalizedRealPolynomialChart N (fun i => homogeneousComponent (weight i) (poly i))
          (Sum.inr i)) =
      homogeneousComponent (weight i) (β (Sum.inr i) - aeval (fun x => β (Sum.inl x)) (poly i)) := by
  rw [normalizedRealPolynomialChart_inr, map_sub, aeval_X, aeval_rename, map_sub]
  congr 1
  exact (weightedTop_aeval (fun _ : X => 1) (fun _ : K => 1)
    (fun x => β (Sum.inl x)) (fun x => hβ (Sum.inl x)) (poly i) (weight i) (hp i)).symm

end Erdos3

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

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_polynomial_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) (i : J j) :
    aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
      (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) -
        C ((c j).val i) =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i +
        integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) := by
  apply MvPolynomial.funext
  intro x
  rw [map_sub, map_add, eval_C, mixedLiftPolynomial_eval]
  change aeval x (aeval _ _) - _ = _
  rw [comp_aeval_apply]
  simp only [aeval_eq_eval]
  rw [← coordinate_eval₂]
  have hspatial : (fun z => aeval x (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl z))) =
      (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) := by
    funext z
    change aeval x (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) z)) = _
    rw [affineFramePolynomial_map, affineFramePolynomial_eval]
    rfl
  have hspatial' := hspatial
  simp only [aeval_eq_eval] at hspatial'
  rw [hspatial']
  have heval := eval₂_algebraMap (S := ℝ)
    (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j)
  have heval' : eval₂ (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) =
      eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) := by
    simpa using heval
  rw [heval']
  exact h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read x j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
      (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)) =
      -homogeneousComponent (j.val + 1)
        (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i) := by
  have hdegree (z : Σ j, J j) :
      coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1) ∈
        weightedSupportLE (fun _ : X => 1) (z.1.val + 1) := by
    apply (mem_weightedSupportLE_iff _ _ _).mpr
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [coeff_coordinate, hp z.1 α hα, map_zero]
  change aeval (fun z => homogeneousComponent
    (Sum.elim (fun _ : X => 1) (fun z : Σ j, J j => z.1.val + 1) z)
    (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
    (normalizedRealPolynomialChart N
      (fun z : Σ j, J j => homogeneousComponent (z.1.val + 1)
        (coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1)))
      (Sum.inr ⟨j, i⟩)) = _
  rw [normalizedRealPolynomialChart_top_inr (fun z : Σ j, J j => z.1.val + 1) N
    (fun z => coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1))
    hdegree _ (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have heq := h.integerFullChart_polynomial_remainder B U b hb o S hR hσ poly hm
    hp c a v sample read j i
  have hres : integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) -
      aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
        (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) =
      -mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i -
        C ((c j).val i) := by linear_combination -heq
  rw [hres, map_sub, map_neg]
  have hcenter : homogeneousComponent (j.val + 1)
      (C ((c j).val i) : MvPolynomial (LayerSamplerVariables G I n B) ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simp
  rw [hcenter, sub_zero]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_normalized_top_tag
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (fun z => freezePolynomial keep fixed
            (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
      (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)) =
      -homogeneousComponent (j.val + 1)
        (freezePolynomial keep (fun i => (fixed i : ℝ))
          (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i)) := by
  change aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
    (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)))) _ = _
  rw [aeval_frozen_integer_top (fullTaggedVariableWeight J)
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have htop := h.integerFullChart_normalized_top_tag B U b hb o S hR hσ poly hm
    hp c a v sample read N j i
  simp only [integerSampledRealChart] at htop
  rw [htop, map_neg]
  have hdegree : (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j)
      Subtype.val (sample j) i).totalDegree ≤ j.val + 1 :=
    mixedLiftPolynomial_degree (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j) (fun d => d.property) i
  rw [freezePolynomial_top keep _ hdegree]

end Erdos3.VectorPolynomial

end

end OAI
