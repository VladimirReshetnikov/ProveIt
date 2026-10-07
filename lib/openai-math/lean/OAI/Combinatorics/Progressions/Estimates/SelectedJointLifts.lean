import OAI.Combinatorics.Progressions.Geometry.SelectedCenteredJointSupport
import OAI.Combinatorics.Progressions.Lattices.RoundedAffineLifts

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem translatedSelectedPhysicalDensity_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (c : ∀ j, U j)
    (hc : center = -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
      (constantCoefficientArray U (fun s => c s.1))))
    (z : Option (LayerSamplerVariables G I n B) × V → ℤ)
    (hz : translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ center p hm z ≠ 0) :
    HasQuarterAffinePolynomialLifts p (fun j => (c j).val) (fun k v => (z (k,v) : ℝ))
      (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀)) := by
  apply allocatedAffineDensity_quarter_lifts B U b hb o hR hσ
    (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c hσ1 C hC hchart hsmall hp
  change selectedCoefficientDensity B U b hb o R σ hR hσ L₀
    (centeredAffineCoefficientTorus U p hm c (fun k v => (z (k,v) : ℝ))) ≠ 0
  rw [centeredAffineCoefficientTorus_eq_subtractive, ← hc]
  exact hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)

noncomputable def jointSelectedPhysicalDensity
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (a : X → ℤ) :
    (Option (LayerSamplerVariables G I n B) × X → ℤ) → ℝ :=
  translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ (coefficientConstantCenter U center)
    (fun j => translate (fun i => (a i : ℝ)) (p j))
    (fun j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in
theorem jointSelectedPhysicalDensity_nonneg
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (a : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center a z :=
  translatedSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ _ _ _ _

theorem exists_selectedJointFiniteLaw_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (A : Finset (X → ℤ)) (hA : A.Nonempty)
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X modulus))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hD : 0 < selectedJointDensityMass A modulus T W
      (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center)) :
    ∃ c : ∀ j, U j, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z : A × rectangularWeightIndices 0 W 1,
        0 < (selectedJointFiniteLaw A hA modulus T W hW hZ
          (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center)
          (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) hD).weight z →
        HasQuarterAffinePolynomialLifts p (fun j => (c j).val)
          (fun k i => (jointIntegerFrame (z.1.val,z.2.val) k i : ℝ))
          (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀)) := by
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  refine ⟨c, hc, ?_⟩
  intro z hz
  have hd := (selectedJointFiniteLaw_support A hA modulus T W hW hZ
    (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center)
    (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm center) hD z hz).2
  apply HasQuarterAffinePolynomialLifts.joint_frame z.1.val z.2.val
  exact translatedSelectedPhysicalDensity_lifts B U b hb o R σ hR hσ L₀ hσ1 C hC hchart hsmall
    (fun j => translate (fun i => (z.1.val i : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun i => (z.1.val i : ℝ)) (p j) (hm j))
    (coefficientConstantCenter U center) c hc z.2.val hd.ne'

end Erdos3.VectorPolynomial

end

end OAI
