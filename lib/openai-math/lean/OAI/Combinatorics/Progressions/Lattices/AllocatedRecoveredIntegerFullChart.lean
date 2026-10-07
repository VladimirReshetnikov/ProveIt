import OAI.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
import OAI.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

noncomputable def jointIntegerFullChart : X ⊕ (Σ j, J j) → MvPolynomial K ℤ :=
  Sum.elim (affineFramePolynomial (jointIntegerFrame (a, v))) (fun z => tag z.1 z.2)

theorem jointIntegerFullChart_support
    (htag : ∀ j b, (tag j b).totalDegree ≤ j.val + 1) :
    ∀ i, integerSampledRealChart (jointIntegerFullChart J a v tag) i ∈
      weightedSupportLE (fun _ : K => 1) (fullTaggedVariableWeight J i) := by
  intro i
  apply (mem_weightedSupportLE_one_iff _ _).mpr
  cases i with
  | inl x =>
    change (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)).totalDegree ≤ 1
    exact (totalDegree_map_le _ _).trans (affineFramePolynomial_degree _ _)
  | inr z =>
    change (MvPolynomial.map (Int.castRingHom ℝ) (tag z.1 z.2)).totalDegree ≤ z.1.val + 1
    exact (totalDegree_map_le _ _).trans (htag z.1 z.2)

theorem jointIntegerFullChart_spatial (x : K → ℤ) :
    integerSampledSpatial (jointIntegerFullChart J a v tag) x =
      jointIntegerPhysicalSite x (a, v) := by
  funext i
  change MvPolynomial.aeval x (affineFramePolynomial (jointIntegerFrame (a, v)) i) = _
  rw [affineFramePolynomial_eval]
  have h := congrFun (integerAffineMap_jointIntegerFrame (a, v) x) i
  simpa only [integerAffineMap] using h

theorem cast_jointIntegerPhysicalSite_eq_frame (x : K → ℤ) :
    (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) =
      (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) := by
  rw [← integerAffineMap_jointIntegerFrame]
  funext i
  simp only [integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul]

theorem eval_jointIntegerPhysicalSite_eq_frame
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : VectorPolynomial X ℝ V) (x : K → ℤ) :
    eval (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) p =
      eval (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) p := by
  rw [cast_jointIntegerPhysicalSite_eq_frame]
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
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

noncomputable def allocatedRecoveredIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    X ⊕ (Σ j, J j) → MvPolynomial (LayerSamplerVariables G I n B) ℤ :=
  jointIntegerFullChart J a v
    (coefficientIntegerFloorPolynomial U b o sample
      (centeredAffineCoefficientArray U poly hm c
        (fun k z => (jointIntegerFrame (a, v) k z : ℝ))))

theorem allocatedRecoveredIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ i, integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i ∈
      weightedSupportLE (fun _ : LayerSamplerVariables G I n B => 1) (fullTaggedVariableWeight J i) := by
  apply jointIntegerFullChart_support
  exact coefficientIntegerFloorPolynomial_degree U b o sample _

theorem allocatedRecoveredIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : LayerSamplerVariables G I n B → ℤ) :
    integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x =
      jointIntegerPhysicalSite x (a, v) :=
  jointIntegerFullChart_spatial J a v _ x

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℝ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i =
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩)) := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  have hβ := canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample
    (centeredAffineCoefficientArray U poly hm c frame) hc j i
  change eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i - (c j).val i =
    mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ)
        (coefficientIntegerFloorPolynomial U b o sample
          (centeredAffineCoefficientArray U poly hm c frame) j i))
  rw [← coefficientRowPolynomial_centered_affine_eval U poly hm hp c frame j i x,
    hβ.1, map_add, mixedLiftPolynomial_eval]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k) (j : Fin m) (i : J j) :
    |eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i - (c j).val i -
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ)| ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  rw [eval_jointIntegerPhysicalSite_eq_frame a v,
    ← integerSampledRealChart_eval (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample),
    h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read,
    add_sub_cancel_right]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart
    j (sample j) (h.2.2.1 j).2 (fun k => (x k : ℝ)) hx i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (k : ℕ) (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ z, |(x z : ℝ)| ≤ layerSamplerBox B U b S z)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x i : ℝ)| ≤ 1 / 8 := by
  rw [allocatedRecoveredIntegerFullChart_spatial, lowTaggedPolynomial_eval]
  exact (h.integerFullChart_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hp
    c a v sample read x hx (lowTaggedIndex J k i).1 (lowTaggedIndex J k i).2).trans
      (hsmall (lowTaggedIndex J k i).1)

end Erdos3.VectorPolynomial

end

end OAI
