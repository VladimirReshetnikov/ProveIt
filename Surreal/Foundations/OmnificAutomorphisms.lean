import Surreal.Algebra.ReconstructionAutomorphisms
import Surreal.Foundations.RealStructureReconstruction
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Omnific automorphisms fix actual real coefficients

The extension, order, coefficient, finiteness, infinitesimal and
standard-part assertions of `odg:def:thm:autreal`.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The unique fraction-field extension of an actual omnific ring automorphism. -/
def omnificAutomorphismExtension (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) :
    SignSequence.{u} ≃+* SignSequence.{u} := IsFractionRing.ringEquivOfRingEquiv f

@[simp] theorem omnificAutomorphismExtension_apply_omnific
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (a : OmnificInteger.{u}) :
    omnificAutomorphismExtension f (omnificToSurreal a) = omnificToSurreal (f a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap f a

/-- The extension has exactly the printed fraction formula. -/
theorem omnificAutomorphismExtension_div
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (a b : OmnificInteger.{u}) :
    omnificAutomorphismExtension f (omnificToSurreal a / omnificToSurreal b) =
      omnificToSurreal (f a) / omnificToSurreal (f b) := by
  rw [map_div₀, omnificAutomorphismExtension_apply_omnific, omnificAutomorphismExtension_apply_omnific]

/-- Even among field homomorphisms, agreement on the omnific ring determines the extension. -/
theorem omnificAutomorphismExtension_unique
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (g : SignSequence.{u} →+* SignSequence.{u})
    (hg : ∀ a : OmnificInteger.{u}, g (omnificToSurreal a) = omnificToSurreal (f a)) :
    g = (omnificAutomorphismExtension f).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨a, b, _, _, _, hx⟩ := surreal_eq_omnific_fraction x
  rw [hx, map_div₀, hg, hg]
  exact (omnificAutomorphismExtension_div f a b).symm

@[simp] theorem omnificAutomorphismExtension_symm
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) :
    omnificAutomorphismExtension f.symm = (omnificAutomorphismExtension f).symm := rfl

/-- The reconstructed coefficient predicate is preserved by the extension. -/
theorem omnificAutomorphismExtension_coefficient
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) {x : SignSequence.{u}}
    (hx : RealReconstruction.Coefficient x) :
    RealReconstruction.Coefficient (omnificAutomorphismExtension f x) := by
  obtain ⟨a, b, hab, rfl⟩ := hx
  exact ⟨f a, f b, (IdealReconstruction.coeff_equiv f a b).mpr hab,
    omnificAutomorphismExtension_div f a b⟩

theorem omnificAutomorphismExtension_coefficient_iff
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (x : SignSequence.{u}) :
    RealReconstruction.Coefficient (omnificAutomorphismExtension f x) ↔
      RealReconstruction.Coefficient x := by
  constructor
  · intro h
    have hi := omnificAutomorphismExtension_coefficient f.symm h
    simpa only [omnificAutomorphismExtension_symm, RingEquiv.symm_apply_apply] using hi
  · exact omnificAutomorphismExtension_coefficient f

private theorem exists_real_image (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (r : ℝ) :
    ∃ s : ℝ, omnificAutomorphismExtension f (ofReal r) = ofReal s :=
  (RealReconstruction.coefficient_iff _).mp (omnificAutomorphismExtension_coefficient f
    ((RealReconstruction.coefficient_iff _).mpr ⟨r, rfl⟩))

private def realImage (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (r : ℝ) : ℝ :=
  (exists_real_image f r).choose

private theorem realImage_spec (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (r : ℝ) :
    omnificAutomorphismExtension f (ofReal r) = ofReal (realImage f r) :=
  (exists_real_image f r).choose_spec

private def realRestriction (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) : ℝ →+* ℝ where
  toFun := realImage f
  map_zero' := ofReal.{u}.injective (by
    change ofReal (realImage f 0) = ofReal 0
    rw [← realImage_spec, map_zero, map_zero])
  map_one' := ofReal.{u}.injective (by
    change ofReal (realImage f 1) = ofReal 1
    rw [← realImage_spec, map_one, map_one])
  map_add' r s := ofReal.{u}.injective (by
    change ofReal (realImage f (r + s)) = ofReal (realImage f r + realImage f s)
    rw [← realImage_spec, map_add, map_add, realImage_spec, realImage_spec, map_add])
  map_mul' r s := ofReal.{u}.injective (by
    change ofReal (realImage f (r * s)) = ofReal (realImage f r * realImage f s)
    rw [← realImage_spec, map_mul, map_mul, realImage_spec, realImage_spec, map_mul])

/-- The extension fixes each actual embedded ordinary real, not just the coefficient field setwise. -/
theorem omnificAutomorphismExtension_ofReal
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (r : ℝ) :
    omnificAutomorphismExtension f (ofReal r) = ofReal r := by
  have h : realImage f r = r := Real.ringHom_apply (realRestriction f) r
  rw [realImage_spec, h]

/-- Positivity of squares makes the field extension strictly order preserving. -/
theorem omnificAutomorphismExtension_strictMono (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) :
    StrictMono (omnificAutomorphismExtension f) := by
  have hm := ringHom_monotone (fun x (hx : (0 : SignSequence.{u}) ≤ x) =>
    ⟨sqrt x, by simpa only [pow_two] using (sqrt_sq hx).symm⟩)
    (omnificAutomorphismExtension f).toRingHom
  exact hm.strictMono_of_injective (omnificAutomorphismExtension f).injective

/-- The extension as an automorphism of the actual ordered field. -/
def omnificAutomorphismOrderExtension (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) :
    SignSequence.{u} ≃+*o SignSequence.{u} where
  __ := omnificAutomorphismExtension f
  map_le_map_iff' := (omnificAutomorphismExtension_strictMono f).le_iff_le

/-- The extension preserves and reflects the existing finite-element ring. -/
theorem omnificAutomorphismExtension_finite_iff
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (x : SignSequence.{u}) :
    IsFinite (omnificAutomorphismExtension f x) ↔ IsFinite x := by
  rw [isFinite_iff_exists_nat_abs_le, isFinite_iff_exists_nat_abs_le]
  apply exists_congr
  intro n
  change |omnificAutomorphismOrderExtension f x| ≤ (n : SignSequence) ↔ _
  conv_lhs => rw [← map_abs, ← map_natCast (omnificAutomorphismOrderExtension f) n]
  exact (omnificAutomorphismExtension_strictMono f).le_iff_le

/-- The extension preserves and reflects the existing infinitesimal ideal. -/
theorem omnificAutomorphismExtension_infinitesimal_iff
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) (x : SignSequence.{u}) :
    IsInfinitesimal (omnificAutomorphismExtension f x) ↔ IsInfinitesimal x := by
  rw [isInfinitesimal_iff_forall_real_abs_lt, isInfinitesimal_iff_forall_real_abs_lt]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  change |omnificAutomorphismOrderExtension f x| < ofReal r ↔ _
  conv_lhs => rw [← map_abs, ← omnificAutomorphismExtension_ofReal f r]
  exact (omnificAutomorphismExtension_strictMono f).lt_iff_lt

/-- On finite actual surreals, the extension commutes with standard part. -/
theorem omnificAutomorphismExtension_standardPart
    (f : OmnificInteger.{u} ≃+* OmnificInteger.{u}) {x : SignSequence.{u}} (hx : IsFinite x) :
    standardPart (omnificAutomorphismExtension f x) = standardPart x := by
  have hi := (omnificAutomorphismExtension_infinitesimal_iff f (x - ofReal (standardPart x))).mpr
    (infinitesimal_sub_standardPart hx)
  rw [map_sub, omnificAutomorphismExtension_ofReal] at hi
  exact (infinitesimal_sub_ofReal_iff ((omnificAutomorphismExtension_finite_iff f x).mpr hx)).mp hi

end
end Surreal.Foundations.SignSequence
