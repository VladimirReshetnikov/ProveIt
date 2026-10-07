import OAI.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
import OAI.Combinatorics.Progressions.Estimates.SelectedJointLifts

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem translate_subtractConstant {X R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (h : X → R) (c : V)
    (p : VectorPolynomial X R V) :
    translate h (subtractConstant c p) = subtractConstant c (translate h p) := by
  exact substitute_subtractConstant (fun i => MvPolynomial.X i + MvPolynomial.C (h i)) c p

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem allocatedJointDensity_subtractConstant
    (S : LayerSamplerScale (G := G) B U b R σ)
    (hS : S = selectedLayerSamplerScale B U b R σ hR hσ L₀)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCoefficientDensity B U b hb o hR hσ S
      (affineSampleCoefficientTorus U
        (fun j => translate (fun t => (a t : ℝ)) (subtractConstant (c j).val (p j)))
        (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ))
          (subtractConstant (c j).val (p j))
          (coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)))
        (fun k t => (z (k, t) : ℝ))) =
      jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center a z := by
  subst S
  simpa only [selectedPhysicalDensity, selectedCoefficientDensity,
    jointSelectedPhysicalDensity, hc, translate_subtractConstant] using
    selectedPhysicalDensity_subtractConstant B U b hb o R σ hR hσ L₀
      (fun j => translate (fun t => (a t : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ)) (p j) (hm j)) c z

end Erdos3.VectorPolynomial

end

end OAI
