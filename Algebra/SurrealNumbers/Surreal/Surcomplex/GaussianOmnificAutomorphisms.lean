import Surreal.Surcomplex.GaussianFractionField
import Surreal.Algebra.ReconstructionAutomorphisms

/-!
# Extending Gaussian omnific automorphisms and recovering their coefficient action

The extension and coefficient-preservation clauses of `odg:def:prop:coeffaut`.
The coefficientwise lifting section is constructed in `GaussianCoefficientSection`.
-/

universe u
namespace Surreal.Surcomplex
noncomputable section

/-- The literal reconstructed coefficient predicate on the interpreted Gaussian fraction field. -/
def ReconstructedCoefficient (z : Surcomplex.{u}) : Prop :=
  ∃ a b : GaussianOmnificInteger.{u}, IdealReconstruction.Coeff a b ∧
    z = gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b

/-- The interpreted coefficient predicate is precisely the actual ordinary complex field. -/
theorem reconstructedCoefficient_iff (z : Surcomplex.{u}) :
    ReconstructedCoefficient z ↔ ∃ c : ℂ, z = ofComplex c := by
  constructor
  · rintro ⟨a, b, hc, rfl⟩
    exact ((gaussianOmnific_coefficientFormula_iff a b).mp hc).2
  · intro hz
    obtain ⟨a, b, _, _, hb, he⟩ := surcomplex_eq_gaussianOmnific_fraction z
    refine ⟨a, b, (gaussianOmnific_coefficientFormula_iff a b).mpr ⟨hb, ?_⟩, he⟩
    rwa [← he]

/-- The unique fraction-field extension of a Gaussian omnific ring automorphism. -/
def gaussianOmnificAutomorphismExtension
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) :
    Surcomplex.{u} ≃+* Surcomplex.{u} := IsFractionRing.ringEquivOfRingEquiv f

@[simp] theorem gaussianOmnificAutomorphismExtension_apply
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (a : GaussianOmnificInteger.{u}) :
    gaussianOmnificAutomorphismExtension f (gaussianOmnificToSurcomplex a) =
      gaussianOmnificToSurcomplex (f a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap f a

/-- The field extension is the printed fraction formula. -/
theorem gaussianOmnificAutomorphismExtension_div
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (a b : GaussianOmnificInteger.{u}) :
    gaussianOmnificAutomorphismExtension f
      (gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b) =
      gaussianOmnificToSurcomplex (f a) / gaussianOmnificToSurcomplex (f b) := by
  rw [map_div₀, gaussianOmnificAutomorphismExtension_apply, gaussianOmnificAutomorphismExtension_apply]

/-- Agreement on the Gaussian omnific ring uniquely determines even a field homomorphism. -/
theorem gaussianOmnificAutomorphismExtension_unique
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (g : Surcomplex.{u} →+* Surcomplex.{u})
    (hg : ∀ a, g (gaussianOmnificToSurcomplex a) = gaussianOmnificToSurcomplex (f a)) :
    g = (gaussianOmnificAutomorphismExtension f).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨a, b, _, _, _, hz⟩ := surcomplex_eq_gaussianOmnific_fraction z
  rw [hz, map_div₀, hg, hg]
  exact (gaussianOmnificAutomorphismExtension_div f a b).symm

@[simp] theorem gaussianOmnificAutomorphismExtension_symm
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) :
    gaussianOmnificAutomorphismExtension f.symm = (gaussianOmnificAutomorphismExtension f).symm := rfl

/-- Ring-formula invariance transports the actual reconstructed coefficient field. -/
theorem gaussianOmnificAutomorphismExtension_coefficient
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) {z : Surcomplex.{u}}
    (hz : ReconstructedCoefficient z) : ReconstructedCoefficient (gaussianOmnificAutomorphismExtension f z) := by
  obtain ⟨a, b, hab, rfl⟩ := hz
  exact ⟨f a, f b, (IdealReconstruction.coeff_equiv f a b).mpr hab,
    gaussianOmnificAutomorphismExtension_div f a b⟩

theorem gaussianOmnificAutomorphismExtension_coefficient_iff
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (z : Surcomplex.{u}) :
    ReconstructedCoefficient (gaussianOmnificAutomorphismExtension f z) ↔ ReconstructedCoefficient z := by
  constructor
  · intro hz
    have hi := gaussianOmnificAutomorphismExtension_coefficient f.symm hz
    simpa only [gaussianOmnificAutomorphismExtension_symm, RingEquiv.symm_apply_apply] using hi
  · exact gaussianOmnificAutomorphismExtension_coefficient f

private theorem exists_complex_image
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (c : ℂ) :
    ∃ d : ℂ, gaussianOmnificAutomorphismExtension f (ofComplex c) = ofComplex d :=
  (reconstructedCoefficient_iff _).mp (gaussianOmnificAutomorphismExtension_coefficient f
    ((reconstructedCoefficient_iff _).mpr ⟨c, rfl⟩))

private def complexImage (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (c : ℂ) : ℂ :=
  (exists_complex_image f c).choose

private theorem complexImage_spec (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (c : ℂ) :
    gaussianOmnificAutomorphismExtension f (ofComplex c) = ofComplex (complexImage f c) :=
  (exists_complex_image f c).choose_spec

private def complexRestrictionHom (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) :
    ℂ →+* ℂ where
  toFun := complexImage f
  map_zero' := ofComplex_injective.{u} (by
    change ofComplex (complexImage f 0) = ofComplex 0
    rw [← complexImage_spec, map_zero, map_zero])
  map_one' := ofComplex_injective.{u} (by
    change ofComplex (complexImage f 1) = ofComplex 1
    rw [← complexImage_spec, map_one, map_one])
  map_add' c d := ofComplex_injective.{u} (by
    change ofComplex (complexImage f (c + d)) = ofComplex (complexImage f c + complexImage f d)
    rw [← complexImage_spec, map_add, map_add, complexImage_spec, complexImage_spec, map_add])
  map_mul' c d := ofComplex_injective.{u} (by
    change ofComplex (complexImage f (c * d)) = ofComplex (complexImage f c * complexImage f d)
    rw [← complexImage_spec, map_mul, map_mul, complexImage_spec, complexImage_spec, map_mul])

private theorem complexImage_inverse
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (c : ℂ) :
    complexImage f.symm (complexImage f c) = c := by
  apply ofComplex_injective.{u}
  rw [← complexImage_spec, ← complexImage_spec, gaussianOmnificAutomorphismExtension_symm,
    RingEquiv.symm_apply_apply]

/-- Restriction of every Gaussian omnific automorphism is an actual automorphism of ordinary C. -/
def gaussianOmnificCoefficientAction
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) : ℂ ≃+* ℂ where
  __ := complexRestrictionHom f
  invFun := complexImage f.symm
  left_inv := complexImage_inverse f
  right_inv c := by
    change complexImage f (complexImage f.symm c) = c
    exact complexImage_inverse f.symm c

/-- The restriction square commutes with the canonical ordinary-complex embedding. -/
theorem gaussianOmnificAutomorphismExtension_ofComplex
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (c : ℂ) :
    gaussianOmnificAutomorphismExtension f (ofComplex c) = ofComplex (gaussianOmnificCoefficientAction f c) :=
  complexImage_spec f c

/-- Ordinary complex membership is preserved and reflected by the actual field extension. -/
theorem gaussianOmnificAutomorphismExtension_complex_iff
    (f : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) (z : Surcomplex.{u}) :
    (∃ c : ℂ, gaussianOmnificAutomorphismExtension f z = ofComplex c) ↔ ∃ c : ℂ, z = ofComplex c := by
  rw [← reconstructedCoefficient_iff, ← reconstructedCoefficient_iff]
  exact gaussianOmnificAutomorphismExtension_coefficient_iff f z

/-- Fraction extension respects composition of automorphisms. -/
def gaussianOmnificAutomorphismExtensionHom :
    (GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) →* (Surcomplex.{u} ≃+* Surcomplex.{u}) :=
  IsFractionRing.ringEquivOfRingEquivHom GaussianOmnificInteger.{u} Surcomplex.{u}

/-- The restriction to complex coefficients is a homomorphism of automorphism groups.
Surjectivity requires the separate coefficientwise lift. -/
def gaussianOmnificCoefficientActionHom :
    (GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) →* (ℂ ≃+* ℂ) where
  toFun := gaussianOmnificCoefficientAction
  map_one' := by
    apply RingEquiv.ext
    intro c
    apply ofComplex_injective.{u}
    change ofComplex (gaussianOmnificCoefficientAction 1 c) = ofComplex c
    rw [← gaussianOmnificAutomorphismExtension_ofComplex]
    have h : gaussianOmnificAutomorphismExtension (1 : GaussianOmnificInteger.{u} ≃+* _) = 1 :=
      gaussianOmnificAutomorphismExtensionHom.map_one
    rw [h]
    rfl
  map_mul' f g := by
    apply RingEquiv.ext
    intro c
    apply ofComplex_injective.{u}
    change ofComplex (gaussianOmnificCoefficientAction (f * g) c) =
      ofComplex (gaussianOmnificCoefficientAction f (gaussianOmnificCoefficientAction g c))
    rw [← gaussianOmnificAutomorphismExtension_ofComplex]
    have h : gaussianOmnificAutomorphismExtension (f * g) =
        gaussianOmnificAutomorphismExtension f * gaussianOmnificAutomorphismExtension g :=
      gaussianOmnificAutomorphismExtensionHom.map_mul f g
    rw [h]
    change gaussianOmnificAutomorphismExtension f (gaussianOmnificAutomorphismExtension g (ofComplex c)) = _
    rw [gaussianOmnificAutomorphismExtension_ofComplex, gaussianOmnificAutomorphismExtension_ofComplex]

end
end Surreal.Surcomplex
