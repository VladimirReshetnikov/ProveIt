import Surreal.Algebra.DiophantineConstants
import Surreal.Algebra.QuadraticNormRigidity
import Surreal.Surcomplex.IntersectivePolynomial
import Surreal.Surcomplex.PellRigidity
import Surreal.Foundations.OmnificIntegerDivisors

/-!
# One parameter-free system for actual integer and Gaussian constants

The actual-carrier assertions of `odg:def:thm:constants`. The same literal
predicate, with three equations and five ring-valued witnesses, defines Z
in the omnific integers and Z[i] in the Gaussian omnific integers.
-/

universe u
namespace Surreal

open DiophantineConstants

noncomputable section

namespace Foundations.SignSequence

/-- The literal Xi predicate defines exactly the ordinary integers in the actual omnific ring. -/
theorem omnific_xi_iff (x : Foundations.SignSequence.OmnificInteger.{u}) :
    Xi x ↔ ∃ a : ℤ, x = Foundations.SignSequence.omnificIntCast a := by
  have hiff := xi_iff_mem_range omnificIntCast (fun u v hp => ?_)
    omnific_intersectivePolynomial_ne_zero (fun x w a ha he => ?_) integer_xi x
  · rw [hiff]
    exact exists_congr (fun a => eq_comm)
  · have hp' : u ^ 2 - omnificIntCast 2 * v ^ 2 = omnificIntCast 1 := by
      simpa only [map_ofNat, map_one] using hp
    have hv := (Surcomplex.omnific_pell_rigidity 2 1 (by norm_num) (by norm_num) u v hp').2
    exact ⟨omnificConstantCoeff v, hv.symm⟩
  · have ha0 : a ≠ 0 := by intro hz; apply ha; rw [hz, map_zero]
    obtain ⟨b, hb, _⟩ := (omnific_dvd_int_iff x a ha0).mp ⟨w, he.symm⟩
    exact ⟨b, hb.symm⟩

end Foundations.SignSequence

namespace Surcomplex

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Native Gaussian omnific Pell pairs are their ordinary Gaussian constant coordinates. -/
theorem gaussianOmnific_pell_two_rigidity (u v : GaussianOmnificInteger.{u})
    (h : u ^ 2 - 2 * v ^ 2 = 1) :
    u = gaussianOmnificConstants (gaussianOmnificConstantCoeff u) ∧
      v = gaussianOmnificConstants (gaussianOmnificConstantCoeff v) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) zero_lt_two
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    norm_num at hr
  have hp : u.val ^ 2 - complexConstants (r ^ 2) * v.val ^ 2 =
      complexConstants 1 := by
    have hv : u.val ^ 2 - 2 * v.val ^ 2 = 1 := congrArg Subtype.val h
    simpa only [hr, map_ofNat, map_one] using hv
  have hh := QuadraticNormRigidity.coordinates_constant constantCoeffAlgHom
    nonnegativeSupport_unit_eq_constant r 1 hr0 one_ne_zero u.val v.val hp
  constructor
  · apply Subtype.ext
    change u.val = complexConstants (GaussianInt.toComplex (gaussianOmnificConstantCoeff u))
    rw [gaussianOmnificConstantCoeff_toComplex]
    exact hh.1
  · apply Subtype.ext
    change v.val = complexConstants (GaussianInt.toComplex (gaussianOmnificConstantCoeff v))
    rw [gaussianOmnificConstantCoeff_toComplex]
    exact hh.2

/-- A Gaussian omnific divisor of a nonzero Gaussian constant is Gaussian constant. -/
theorem gaussianOmnific_divisor_mem_constants (x w : GaussianOmnificInteger.{u})
    (a : GaussianInt) (ha : gaussianOmnificConstants.{u} a ≠ 0)
    (he : x * w = gaussianOmnificConstants a) : x ∈ (gaussianOmnificConstants.{u}).range := by
  have ha0 : a ≠ 0 := by intro hz; apply ha; rw [hz, map_zero]
  have hc : GaussianInt.toComplex a ≠ 0 :=
    (map_ne_zero_iff GaussianInt.toComplex GaussianInt.toComplex_injective).mpr ha0
  have hp : x.val * w.val = complexConstants (GaussianInt.toComplex a) := congrArg Subtype.val he
  have hu : IsUnit (x.val * w.val) := hp ▸ (isUnit_iff_ne_zero.mpr hc).map complexConstants
  have hx := nonnegativeSupport_unit_eq_constant x.val (isUnit_of_mul_isUnit_left hu)
  refine ⟨gaussianOmnificConstantCoeff x, Subtype.ext ?_⟩
  change complexConstants (GaussianInt.toComplex (gaussianOmnificConstantCoeff x)) = x.val
  rw [gaussianOmnificConstantCoeff_toComplex]
  exact hx.symm

/-- The identical Xi predicate defines exactly Z[i] in the actual Gaussian omnific ring. -/
theorem gaussianOmnific_xi_iff (x : GaussianOmnificInteger.{u}) :
    Xi x ↔ ∃ a : GaussianInt, x = gaussianOmnificConstants a := by
  have hiff := xi_iff_mem_range gaussianOmnificConstants
    (fun u v hp => ⟨gaussianOmnificConstantCoeff v, (gaussianOmnific_pell_two_rigidity u v hp).2.symm⟩)
    gaussianOmnific_intersectivePolynomial_ne_zero gaussianOmnific_divisor_mem_constants gaussian_xi x
  rw [hiff]
  exact exists_congr (fun a => eq_comm)

end Surcomplex
end
end Surreal
