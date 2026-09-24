import Surreal.Algebra.CentralConicRigidity
import Surreal.Surcomplex.BinaryFormRigidity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Nonsingular central conics over the actual support rings

The coefficient form of `odg:cor:conics`. A general binary quadratic has
coefficients a,b,c and symmetric matrix [[a,b/2],[b/2,c]], whose native
rank-two criterion is proved equivalent to the nonzero discriminant.
The center is given by its two exact linear equations. Nonzero centered
value gives constant complex or real support coordinates and ordinary
integer coordinates for actual omnific solutions.
-/

universe u
namespace Surreal.Surcomplex

open Foundations CentralConic

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Central nonsingular complex conics have constant solutions in the actual complex support ring. -/
theorem nonnegativeSupport_central_conic_rigidity (a b c d e f h k : ℂ)
    (hd : b ^ 2 - 4 * a * c ≠ 0)
    (hh : 2 * a * h + b * k + d = 0) (hk : b * h + 2 * c * k + e = 0)
    (hl : value a b c d e f h k ≠ 0) (x y : nonnegativeSupportSubring.{u})
    (he : value (complexConstants a) (complexConstants b) (complexConstants c)
      (complexConstants d) (complexConstants e) (complexConstants f) x y = 0) :
    x = complexConstants (constantCoeff x) ∧ y = complexConstants (constantCoeff y) :=
  CentralConic.coordinates_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    a b c d e f h k hd hh hk hl x y he

/-- Include the actual real support ring in its complexification. -/
def realSupportInclusion : SignSequence.nonnegativeSupportSubring.{u} →+*
    nonnegativeSupportSubring.{u} :=
  (ofReal.comp SignSequence.nonnegativeSupportSubring.subtype).codRestrict _
    (fun x => ⟨x.property, Subring.zero_mem _⟩)

@[simp] theorem realSupportInclusion_realConstants (r : ℝ) :
    realSupportInclusion (SignSequence.realConstants.{u} r) = complexConstants (r : ℂ) := by
  apply Subtype.ext
  exact (ofComplex_ofReal r).symm

@[simp] theorem constantCoeff_realSupportInclusion (x : SignSequence.nonnegativeSupportSubring.{u}) :
    constantCoeff (realSupportInclusion x) = (SignSequence.constantCoeff x : ℂ) := by
  apply Complex.ext
  · rfl
  · exact map_zero SignSequence.constantCoeff

/-- The real support-ring conclusion for every nonsingular central real conic. -/
theorem realSupport_central_conic_rigidity (a b c d e f h k : ℝ)
    (hd : b ^ 2 - 4 * a * c ≠ 0)
    (hh : 2 * a * h + b * k + d = 0) (hk : b * h + 2 * c * k + e = 0)
    (hl : value a b c d e f h k ≠ 0) (x y : SignSequence.nonnegativeSupportSubring.{u})
    (he : value (SignSequence.realConstants a) (SignSequence.realConstants b)
      (SignSequence.realConstants c) (SignSequence.realConstants d)
      (SignSequence.realConstants e) (SignSequence.realConstants f) x y = 0) :
    x = SignSequence.realConstants (SignSequence.constantCoeff x) ∧
      y = SignSequence.realConstants (SignSequence.constantCoeff y) := by
  have hd' : (b : ℂ) ^ 2 - 4 * a * c ≠ 0 := by exact_mod_cast hd
  have hh' : 2 * (a : ℂ) * h + b * k + d = 0 := by exact_mod_cast hh
  have hk' : (b : ℂ) * h + 2 * c * k + e = 0 := by exact_mod_cast hk
  have hl' : value (a : ℂ) b c d e f h k ≠ 0 := by
    dsimp only [value] at hl ⊢
    exact_mod_cast hl
  have he' := congrArg realSupportInclusion he
  simp only [map_value, realSupportInclusion_realConstants, map_zero] at he'
  obtain ⟨hx, hy⟩ := nonnegativeSupport_central_conic_rigidity
    a b c d e f h k hd' hh' hk' hl' (realSupportInclusion x) (realSupportInclusion y) he'
  constructor
  · apply Subtype.ext
    have hv := congrArg (fun z : nonnegativeSupportSubring => z.val.re) hx
    rw [constantCoeff_realSupportInclusion] at hv
    exact hv
  · apply Subtype.ext
    have hv := congrArg (fun z : nonnegativeSupportSubring => z.val.re) hy
    rw [constantCoeff_realSupportInclusion] at hv
    exact hv

/-- Integer-coefficient central conics have only ordinary actual omnific solutions.
The center itself may have arbitrary ordinary real coordinates. -/
theorem omnific_central_conic_rigidity (a b c d e f : ℤ) (h k : ℝ)
    (hd : b ^ 2 - 4 * a * c ≠ 0)
    (hh : 2 * (a : ℝ) * h + b * k + d = 0) (hk : (b : ℝ) * h + 2 * c * k + e = 0)
    (hl : value (a : ℝ) b c d e f h k ≠ 0) (x y : SignSequence.OmnificInteger.{u})
    (he : value (SignSequence.omnificIntCast a) (SignSequence.omnificIntCast b)
      (SignSequence.omnificIntCast c) (SignSequence.omnificIntCast d)
      (SignSequence.omnificIntCast e) (SignSequence.omnificIntCast f) x y = 0) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  have hd' : (b : ℝ) ^ 2 - 4 * a * c ≠ 0 := by exact_mod_cast hd
  have he' := congrArg SignSequence.omnificSubring.subtype he
  rw [map_value, map_zero] at he'
  obtain ⟨hx, hy⟩ := realSupport_central_conic_rigidity
    a b c d e f h k hd' hh hk hl x.val y.val he'
  constructor
  · apply SignSequence.omnific_eq_intConstant_of_finite
    have hv := congrArg Subtype.val hx
    change SignSequence.omnificToSurreal x = SignSequence.ofReal _ at hv
    rw [hv]
    exact SignSequence.finite_ofReal _
  · apply SignSequence.omnific_eq_intConstant_of_finite
    have hv := congrArg Subtype.val hy
    change SignSequence.omnificToSurreal y = SignSequence.ofReal _ at hv
    rw [hv]
    exact SignSequence.finite_ofReal _

/-- The source's real-support conclusion with native rank two and its literal center identity. -/
theorem realSupport_central_conic_of_rank_two (a b c d e f h k : ℝ)
    (hrank : Matrix.rank (!![a, b / 2; b / 2, c]) = 2)
    (hcenter : ∀ u v : ℝ, value a b c d e f (h + u) (k + v) =
      a * u ^ 2 + b * u * v + c * v ^ 2 + value a b c d e f h k)
    (hl : value a b c d e f h k ≠ 0) (x y : SignSequence.nonnegativeSupportSubring.{u})
    (he : value (SignSequence.realConstants a) (SignSequence.realConstants b)
      (SignSequence.realConstants c) (SignSequence.realConstants d)
      (SignSequence.realConstants e) (SignSequence.realConstants f) x y = 0) :
    x = SignSequence.realConstants (SignSequence.constantCoeff x) ∧
      y = SignSequence.realConstants (SignSequence.constantCoeff y) := by
  obtain ⟨hh, hk⟩ := (center_iff a b c d e f h k).mp hcenter
  exact realSupport_central_conic_rigidity a b c d e f h k
    ((BinaryFormRigidity.binaryQuadratic_rank_two_iff a b c).mp hrank) hh hk hl x y he

/-- The source's integer-coefficient conclusion, again with native real matrix rank and
the center's ordinary real translation identity. -/
theorem omnific_central_conic_of_rank_two (a b c d e f : ℤ) (h k : ℝ)
    (hrank : Matrix.rank (!![(a : ℝ), b / 2; b / 2, (c : ℝ)]) = 2)
    (hcenter : ∀ u v : ℝ, value (a : ℝ) b c d e f (h + u) (k + v) =
      a * u ^ 2 + b * u * v + c * v ^ 2 + value (a : ℝ) b c d e f h k)
    (hl : value (a : ℝ) b c d e f h k ≠ 0) (x y : SignSequence.OmnificInteger.{u})
    (he : value (SignSequence.omnificIntCast a) (SignSequence.omnificIntCast b)
      (SignSequence.omnificIntCast c) (SignSequence.omnificIntCast d)
      (SignSequence.omnificIntCast e) (SignSequence.omnificIntCast f) x y = 0) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  have hd := (BinaryFormRigidity.binaryQuadratic_rank_two_iff (a : ℝ) b c).mp hrank
  have hd' : b ^ 2 - 4 * a * c ≠ 0 := by exact_mod_cast hd
  obtain ⟨hh, hk⟩ := (center_iff (a : ℝ) b c d e f h k).mp hcenter
  exact omnific_central_conic_rigidity a b c d e f h k hd' hh hk hl x y he

end
end Surreal.Surcomplex
