import Surreal.HahnSeries.NonpositiveSupportUnits
import Surreal.HahnSeries.NonpositiveCoefficientExtension
import Surreal.Algebra.ProductNormRigidity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharZero.Infinite

/-!
# Finite étale norm rigidity in arbitrary Hahn intermediate rings

Completes the general set-sized Hahn-ring assertion of `odg:dec:thm:etale`.
The coefficient field need not be algebraically closed, and the ordered
abelian exponent group need not be divisible or nontrivial. Extend
coefficients to an algebraic closure, apply the proved constant-unit norm
rigidity, and descend constancy along the injective coefficient map.
The support convention is increasing t-exponents, hence support ≤ 0.
-/

namespace Surreal.HahnSeries

open Module

noncomputable section

variable {Γ F K H J : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field F] [CharZero F] [Field K] [Algebra F K]
  [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
  {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra F (L h)]
  [∀ h, Module.Finite F (L h)]

attribute [local instance] nonpositiveSupportAlgebra

/-- A nonzero constant norm level in any nonpositive-support Hahn ring forces constant
coordinates, for every finite product of finite extensions and every basis. -/
theorem nonpositiveSupport_etale_norm_rigidity (b : Basis J F (∀ h, L h))
    (c : K) (hc : c ≠ 0) (x : J → nonpositiveSupportSubring Γ K)
    (hx : (NormForm.polynomial b).eval₂ (nonpositiveConstants.comp (algebraMap F K)) x =
      nonpositiveConstants c) :
    ∀ j, x j = nonpositiveConstants (nonpositiveConstantCoeff (x j)) := by
  let E := AlgebraicClosure K
  let φ : K →+* E := algebraMap K E
  letI : Algebra F E := (φ.comp (algebraMap F K)).toAlgebra
  let ψ := nonpositiveMapCoefficients (Γ := Γ) φ
  have hcoeff : ψ.comp (nonpositiveConstants.comp (algebraMap F K)) =
      (nonpositiveConstants (Γ := Γ)).comp (algebraMap F E) := by
    apply RingHom.ext
    intro a
    exact nonpositiveMapCoefficients_constants (Γ := Γ) φ (algebraMap F K a)
  have he : (NormForm.polynomial b).eval₂
      ((nonpositiveConstants (Γ := Γ)).comp (algebraMap F E)) (fun j => ψ (x j)) =
        nonpositiveConstants (φ c) := by
    have h := congrArg ψ hx
    rw [MvPolynomial.hom_eval₂, hcoeff] at h
    simpa only [ψ, nonpositiveMapCoefficients_constants] using h
  have hh := NormForm.etale_coordinates_constant
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := E)) nonpositiveSupport_unit_eq_constant
    b (φ c) (map_ne_zero_iff φ φ.injective |>.mpr hc) (fun j => ψ (x j)) he
  intro j
  exact ((nonpositiveMapCoefficients_eq_constant_iff φ φ.injective (x j)
    (nonpositiveConstantCoeff (ψ (x j)))).mp (hh j)).1

/-- An arbitrary intermediate ring needs only the prescribed intersection with constants;
no constant-term retraction on that intermediate ring is assumed. -/
theorem intermediate_etale_norm_rigidity (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (b : Basis J F (∀ h, L h)) (c : K) (hc : c ≠ 0) (x : J → A)
    (hx : (NormForm.polynomial b).eval₂ (nonpositiveConstants.comp (algebraMap F K))
      (fun j => (x j : nonpositiveSupportSubring Γ K)) = nonpositiveConstants c) :
    ∀ j, ∃ a : o, (x j : nonpositiveSupportSubring Γ K) = nonpositiveConstants (a : K) := by
  have he := nonpositiveSupport_etale_norm_rigidity b c hc (fun j => (x j).val) hx
  intro j
  have hm : nonpositiveConstantCoeff (x j).val ∈ o :=
    (hA _).mp (by rw [← he j]; exact (x j).property)
  exact ⟨⟨nonpositiveConstantCoeff (x j).val, hm⟩, he j⟩

/-- The same theorem for any algebra equipped with a finite-product presentation, transporting
its given basis rather than requiring a literal product carrier. -/
theorem intermediate_etale_norm_rigidity_of_equiv {T : Type*} [CommRing T] [Algebra F T]
    (e : T ≃ₐ[F] (∀ h, L h)) (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (b : Basis J F T) (c : K) (hc : c ≠ 0) (x : J → A)
    (hx : (NormForm.polynomial b).eval₂ (nonpositiveConstants.comp (algebraMap F K))
      (fun j => (x j : nonpositiveSupportSubring Γ K)) = nonpositiveConstants c) :
    ∀ j, ∃ a : o, (x j : nonpositiveSupportSubring Γ K) = nonpositiveConstants (a : K) := by
  apply intermediate_etale_norm_rigidity A o hA (b.map e.toLinearEquiv) c hc x
  simpa only [NormForm.polynomial_basis_map] using hx

end
end Surreal.HahnSeries
