import Surreal.Foundations.OmnificPrincipalQuotients

/-!
# Large principal quotients and their small images

The examples following `osq:prop:principal`, using `osq:thm:reflection`.
The nonzero quotients by omega, omega+2 and omega+1 are not small.
The first two nevertheless map onto Z and Z/2Z, respectively, while the
third has no nonzero small unital ring image.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The ordinary quotient of the image ideal is the residue ring of the constant coefficient. -/
def omnificPrincipalConstantQuotientEquiv (f : OmnificInteger.{u}) :
    (ℤ ⧸ (Ideal.span {f}).map omnificConstantCoeff) ≃+* ZMod (omnificConstantCoeff f).natAbs :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    (Int.quotientSpanEquivZMod (omnificConstantCoeff f))

/-- Every principal quotient maps to the ordinary residue ring specified by its constant. -/
def omnificPrincipalQuotientReflection (f : OmnificInteger.{u}) :
    (OmnificInteger.{u} ⧸ Ideal.span {f}) →+* ZMod (omnificConstantCoeff f).natAbs :=
  (omnificPrincipalConstantQuotientEquiv f).toRingHom.comp
    (omnificQuotientReflection (Ideal.span {f}))

/-- This small reflection is onto even when the original principal quotient is large. -/
theorem omnificPrincipalQuotientReflection_surjective (f : OmnificInteger.{u}) :
    Function.Surjective (omnificPrincipalQuotientReflection f) :=
  (omnificPrincipalConstantQuotientEquiv f).surjective.comp
    (QuotientReflection.reflection_surjective omnificConstantCoeff
      omnificConstantCoeff_surjective (Ideal.span {f}))

/-- A unit constant term makes all small unital images of a principal quotient trivial. -/
theorem omnific_principal_no_small_ringHom (f : OmnificInteger.{u})
    (hf : IsUnit (omnificConstantCoeff f)) (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty ((OmnificInteger.{u} ⧸ Ideal.span {f}) →+* S) := by
  rintro ⟨φ⟩
  have he := omnific_small_ringHom_eq_constant (φ.comp (Ideal.Quotient.mk (Ideal.span {f}))) f
  have hz : (omnificConstantCoeff f : S) = 0 := by
    rw [← he]
    change φ (Ideal.Quotient.mk (Ideal.span {f}) f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f), map_zero]
  exact (hf.map (Int.castRingHom S)).ne_zero hz

/-- The manuscript's family of generators n+omega. -/
def omnificShiftedOmega (n : ℤ) : OmnificInteger.{u} :=
  omnificIntCast n + omnificMonomial 1 zero_lt_one

@[simp] theorem omnificShiftedOmega_constant (n : ℤ) :
    omnificConstantCoeff (omnificShiftedOmega.{u} n) = n := by
  have hz := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  change omnificConstantCoeff (omnificMonomial 1 zero_lt_one) = 0 at hz
  rw [omnificShiftedOmega, map_add, omnificConstantCoeff_intCast, hz, _root_.add_zero]

/-- Adding any integer constant leaves a genuinely nonconstant omnific generator. -/
theorem omnificShiftedOmega_nonconstant (n : ℤ) :
    ¬ ∃ m : ℤ, omnificShiftedOmega.{u} n = omnificIntCast m := by
  rintro ⟨m, hm⟩
  have hc := congrArg omnificConstantCoeff hm
  rw [omnificShiftedOmega_constant, omnificConstantCoeff_intCast] at hc
  subst m
  have hz : omnificMonomial (1 : SignSequence.{u}) zero_lt_one = 0 := by
    apply _root_.add_left_cancel (a := omnificIntCast n)
    simpa only [omnificShiftedOmega, _root_.add_zero] using hm
  exact omnificMonomial_ne_zero 1 zero_lt_one hz

/-- Each shifted monomial gives a nonzero large quotient with the stated ordinary residue image. -/
theorem omnificShiftedOmega_quotient (n : ℤ) :
    Nontrivial (OmnificInteger.{u} ⧸ Ideal.span {omnificShiftedOmega n}) ∧
      ¬ Small.{u} (OmnificInteger.{u} ⧸ Ideal.span {omnificShiftedOmega n}) ∧
      ∃ φ : (OmnificInteger.{u} ⧸ Ideal.span {omnificShiftedOmega n}) →+* ZMod n.natAbs,
        Function.Surjective φ := by
  refine ⟨omnific_principal_quotient_nontrivial _ (omnificShiftedOmega_nonconstant n),
    omnific_principal_not_small_of_degree_pos _
      (omnific_leadingExponent_pos_of_nonconstant _ (omnificShiftedOmega_nonconstant n)), ?_⟩
  rw [← congrArg Int.natAbs (omnificShiftedOmega_constant.{u} n)]
  exact ⟨omnificPrincipalQuotientReflection _, omnificPrincipalQuotientReflection_surjective _⟩

/-- The nonzero quotient by one plus omega has no nonzero small unital image. -/
theorem omnific_one_add_omega_quotient_no_small_ringHom (S : Type v)
    [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty ((OmnificInteger.{u} ⧸ Ideal.span {omnificShiftedOmega 1}) →+* S) :=
  omnific_principal_no_small_ringHom _ (by rw [omnificShiftedOmega_constant]; exact isUnit_one) S

end
end Surreal.Foundations.SignSequence
