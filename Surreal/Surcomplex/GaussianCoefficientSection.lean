import Surreal.Surcomplex.CoefficientAutomorphisms
import Surreal.Algebra.ConstantTermHomomorphisms

/-!
# The coefficient action of Gaussian omnific automorphisms has a section

Completes `odg:def:prop:coeffaut`: every complex automorphism lifts
coefficientwise, preserves the actual Gaussian omnific ring, and supplies
a composition-preserving section of restriction to ordinary coefficients.
-/

universe u
namespace Surreal.Surcomplex
noncomputable section

/-- An arbitrary complex automorphism preserves the embedded Gaussian integer ring. -/
theorem complexAutomorphism_gaussian (σ : ℂ ≃+* ℂ) (a : GaussianInt) :
    ∃ b : GaussianInt, GaussianInt.toComplex b = σ (GaussianInt.toComplex a) := by
  rcases ConstantTermGraph.gaussian_hom_eq_or_conjugate GaussianInt.toComplex
    (σ.toRingHom.comp GaussianInt.toComplex) with h | h
  · exact ⟨a, (RingHom.congr_fun h a).symm⟩
  · exact ⟨star a, (RingHom.congr_fun h a).symm⟩

/-- Constant extraction transforms by the chosen coefficient automorphism. -/
theorem constantCoeff_coefficientAutomorphism (σ : ℂ ≃+* ℂ) (z : nonnegativeSupportSubring.{u}) :
    constantCoeff ⟨coefficientAutomorphism σ z.val, coefficientAutomorphism_mem_supportRing σ z.property⟩ =
      σ (constantCoeff z) := by
  rw [← supportHahnEmbedding_constantCoeff, ← supportHahnEmbedding_constantCoeff z]
  change (rawNormalForm (coefficientAutomorphism σ z.val)).coeff 0 = σ ((rawNormalForm z.val).coeff 0)
  exact coeff_coefficientAutomorphism σ z.val 0

private def gaussianCoefficientMap (σ : ℂ ≃+* ℂ) (z : GaussianOmnificInteger.{u}) :
    GaussianOmnificInteger.{u} :=
  ⟨⟨coefficientAutomorphism σ z.val.val, coefficientAutomorphism_mem_supportRing σ z.val.property⟩, by
    change ∃ b : GaussianInt, GaussianInt.toComplex b = constantCoeff _
    rw [constantCoeff_coefficientAutomorphism]
    obtain ⟨a, ha⟩ := z.property
    rw [← ha]
    exact complexAutomorphism_gaussian σ a⟩

/-- Restrict the coefficientwise field lift to the actual Gaussian omnific ring. -/
def gaussianCoefficientLift (σ : ℂ ≃+* ℂ) :
    GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u} where
  toFun := gaussianCoefficientMap σ
  invFun := gaussianCoefficientMap σ.symm
  left_inv z := by
    apply gaussianOmnificToSurcomplex_injective
    exact coefficientAutomorphism_inverse σ (gaussianOmnificToSurcomplex z)
  right_inv z := by
    apply gaussianOmnificToSurcomplex_injective
    exact coefficientAutomorphism_inverse σ.symm (gaussianOmnificToSurcomplex z)
  map_add' z w := by
    apply gaussianOmnificToSurcomplex_injective
    change coefficientAutomorphism σ (gaussianOmnificToSurcomplex (z + w)) =
      gaussianOmnificToSurcomplex (gaussianCoefficientMap σ z + gaussianCoefficientMap σ w)
    rw [map_add, map_add, map_add]
    rfl
  map_mul' z w := by
    apply gaussianOmnificToSurcomplex_injective
    change coefficientAutomorphism σ (gaussianOmnificToSurcomplex (z * w)) =
      gaussianOmnificToSurcomplex (gaussianCoefficientMap σ z * gaussianCoefficientMap σ w)
    rw [map_mul, map_mul, map_mul]
    rfl

@[simp] theorem gaussianOmnificToSurcomplex_coefficientLift (σ : ℂ ≃+* ℂ)
    (z : GaussianOmnificInteger.{u}) :
    gaussianOmnificToSurcomplex (gaussianCoefficientLift σ z) =
      coefficientAutomorphism σ (gaussianOmnificToSurcomplex z) := rfl

/-- Fraction extension recovers exactly the coefficientwise field lift. -/
@[simp] theorem gaussianOmnificAutomorphismExtension_coefficientLift (σ : ℂ ≃+* ℂ) :
    gaussianOmnificAutomorphismExtension (gaussianCoefficientLift.{u} σ) = coefficientAutomorphism σ := by
  apply RingEquiv.toRingHom_injective
  exact (gaussianOmnificAutomorphismExtension_unique _ (coefficientAutomorphism σ).toRingHom
    (fun _ => rfl)).symm

/-- The lift is a right inverse of the previously constructed coefficient restriction. -/
@[simp] theorem gaussianOmnificCoefficientAction_coefficientLift (σ : ℂ ≃+* ℂ) :
    gaussianOmnificCoefficientAction (gaussianCoefficientLift.{u} σ) = σ := by
  apply RingEquiv.ext
  intro c
  apply ofComplex_injective.{u}
  rw [← gaussianOmnificAutomorphismExtension_ofComplex,
    gaussianOmnificAutomorphismExtension_coefficientLift, coefficientAutomorphism_ofComplex]

/-- The coefficient section preserves identity and composition in the native automorphism groups. -/
def gaussianCoefficientLiftHom :
    (ℂ ≃+* ℂ) →* (GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) where
  toFun := gaussianCoefficientLift
  map_one' := by
    apply RingEquiv.ext
    intro z
    apply gaussianOmnificToSurcomplex_injective
    change coefficientAutomorphism 1 (gaussianOmnificToSurcomplex z) = gaussianOmnificToSurcomplex z
    have h : coefficientAutomorphism (1 : ℂ ≃+* ℂ) = (1 : Surcomplex.{u} ≃+* Surcomplex.{u}) :=
      coefficientAutomorphismHom.map_one
    rw [h]
    rfl
  map_mul' σ ρ := by
    apply RingEquiv.ext
    intro z
    apply gaussianOmnificToSurcomplex_injective
    change coefficientAutomorphism (σ * ρ) (gaussianOmnificToSurcomplex z) =
      coefficientAutomorphism σ (coefficientAutomorphism ρ (gaussianOmnificToSurcomplex z))
    have h : coefficientAutomorphism (σ * ρ) =
        coefficientAutomorphism.{u} σ * coefficientAutomorphism ρ := coefficientAutomorphismHom.map_mul σ ρ
    rw [h]
    rfl

/-- The native group homomorphisms compose to the identity on complex automorphisms. -/
theorem gaussianCoefficientAction_comp_lift :
    gaussianOmnificCoefficientActionHom.comp gaussianCoefficientLiftHom.{u} = MonoidHom.id (ℂ ≃+* ℂ) := by
  apply MonoidHom.ext
  intro σ
  exact gaussianOmnificCoefficientAction_coefficientLift σ

/-- Every complex field automorphism is induced by an actual Gaussian omnific automorphism. -/
theorem gaussianOmnificCoefficientAction_surjective :
    Function.Surjective (gaussianOmnificCoefficientAction.{u}) :=
  fun σ => ⟨gaussianCoefficientLift σ, gaussianOmnificCoefficientAction_coefficientLift σ⟩

/-- Distinct complex automorphisms give distinct Gaussian omnific automorphisms. -/
theorem gaussianCoefficientLift_injective : Function.Injective (gaussianCoefficientLift.{u}) := by
  intro σ ρ h
  have he := congrArg gaussianOmnificCoefficientAction h
  simpa only [gaussianOmnificCoefficientAction_coefficientLift] using he

end
end Surreal.Surcomplex
