import OAI.Combinatorics.Progressions.Estimates.SelectedJointLifts

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

theorem substitute_translate_joint_frame {K X V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V] (p : VectorPolynomial X ℝ V)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    substitute (affineParameterSubstitution (fun k v => (z (k,v) : ℝ)))
      (translate (fun v => (a v : ℝ)) p) =
    substitute (affineParameterSubstitution
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ))) p := by
  change substitute _ (substitute (fun v => MvPolynomial.X v + MvPolynomial.C (a v : ℝ)) p) = _
  rw [substitute_comp]
  apply congrArg (fun f : X → MvPolynomial K ℝ => substitute f p)
  funext v
  simp only [map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    affineParameterSubstitution, rowPolynomial, jointIntegerFrame, Int.cast_add, map_add,
    MvPolynomial.algebraMap_eq]
  ring

theorem affineSampleCoefficientArray_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientArray U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientArray U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  funext s
  apply Subtype.ext
  simp only [affineSampleCoefficientArray_val, substitute_translate_joint_frame]

theorem affineSampleCoefficientTorus_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientTorus U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientTorus U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) :=
  congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_joint_frame U p hm a z)

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem jointSelectedPhysicalDensity_function
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center =
      fun (a : X → ℤ) => translatedSelectedPhysicalDensity (X := X) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center)
        (fun j => translate (fun t => (a t : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ)) (p j) (hm j)) := rfl

theorem jointSelectedPhysicalDensity_eq_allocated
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center a z =
      allocatedAffineDensity B U b hb o hR hσ
        (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm c
        (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  unfold jointSelectedPhysicalDensity translatedSelectedPhysicalDensity allocatedAffineDensity
  rw [centeredAffineCoefficientTorus_eq_subtractive, ← hc,
    affineSampleCoefficientTorus_joint_frame]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

theorem affineCoefficientCoverSample_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) (q : ℕ) :
    affineCoefficientCoverSample U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      q (fun k v => (z (k,v) : ℝ)) =
    affineCoefficientCoverSample U p hm q
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  unfold affineCoefficientCoverSample
  rw [affineSampleCoefficientArray_joint_frame]

end Erdos3.VectorPolynomial

end

end OAI
