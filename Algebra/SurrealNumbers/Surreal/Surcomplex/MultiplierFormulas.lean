import Surreal.Algebra.IdealReconstruction
import Surreal.Surcomplex.SupportFractionFields
import Surreal.Surcomplex.QuadraticIdealDefinition

/-!
# Internal reconstruction on actual omnific carriers

The fraction-pair formulas of `odg:def:cor:internal` on actual omnific
and Gaussian omnific integers. The formulas mention only ring operations
and ordinary numerals, and every quantified witness lies in the original ring.
-/

universe u
namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

/-- The existing omnific quadratic test is exactly the actual purely infinite predicate. -/
theorem omnific_inf_iff (x : OmnificInteger.{u}) :
    IdealReconstruction.Inf x ↔ IsPurelyInfinite (omnificToSurreal x) := by
  change (∃ y : OmnificInteger, x ^ 2 = 2 * y ^ 2) ↔ IsPurelyInfinite x.val.val
  rw [isPurelyInfinite_iff, ← omnific_purelyInfinite_iff_quadratic]
  exact CoefficientPullback.mem_ker_iff constantCoeff (Int.castRingHom ℝ) Int.cast_injective x

/-- Every actual purely infinite surreal has an omnific representative. -/
theorem IsPurelyInfinite.exists_omnific {x : SignSequence.{u}} (hx : IsPurelyInfinite x) :
    ∃ y : OmnificInteger.{u}, omnificToSurreal y = x := by
  let a : nonnegativeSupportSubring.{u} := ⟨x, hx.mem_supportRing⟩
  have ha : constantCoeff a = 0 := (isPurelyInfinite_iff a).mp hx
  exact ⟨⟨a, ⟨0, by rw [map_zero]; exact ha.symm⟩⟩, rfl⟩

/-- Mult defines the actual real support ring on fraction representatives. -/
theorem omnific_multiplierFormula_iff (a b : OmnificInteger.{u}) :
    IdealReconstruction.Mult a b ↔ b ≠ 0 ∧
      omnificToSurreal a / omnificToSurreal b ∈ nonnegativeSupportSubring := by
  rw [IdealReconstruction.mult_iff omnificToSurreal omnificToSurreal_injective IsPurelyInfinite
    omnific_inf_iff (fun _ hx => hx.exists_omnific)]
  exact and_congr Iff.rfl (purelyInfiniteMultiplier_iff _)

/-- Coeff defines the actual embedded ordinary real field, including zero. -/
theorem omnific_coefficientFormula_iff (a b : OmnificInteger.{u}) :
    IdealReconstruction.Coeff a b ↔ b ≠ 0 ∧
      ∃ r : ℝ, omnificToSurreal a / omnificToSurreal b = ofReal r :=
  IdealReconstruction.coeff_iff omnificToSurreal omnificToSurreal_injective IsPurelyInfinite
    (fun x => ∃ r : ℝ, x = ofReal r) omnific_inf_iff (fun _ hx => hx.exists_omnific)
    real_iff_multiplier_and_inverse a b

/-- The actual coefficient map is reconstructed by subtraction into the purely infinite ideal. -/
theorem coefficientGraph_iff (x : nonnegativeSupportSubring.{u}) (r : ℝ) :
    IsPurelyInfinite (x.val - ofReal r) ↔ r = constantCoeff x := by
  change IsPurelyInfinite (x - realConstants r).val ↔ _
  rw [isPurelyInfinite_iff]
  change constantCoeff (x - realConstants r) = 0 ↔ _
  rw [map_sub, constantCoeff_realConstants, sub_eq_zero, eq_comm]

/-- The literal four-coordinate pair formula is the graph of actual coefficient extraction. -/
theorem omnific_reconstructionGraph_iff (a b c d : OmnificInteger.{u}) :
    IdealReconstruction.Graph a b c d ↔ b ≠ 0 ∧ d ≠ 0 ∧
      ∃ x : nonnegativeSupportSubring.{u},
        omnificToSurreal a / omnificToSurreal b = x.val ∧
        omnificToSurreal c / omnificToSurreal d = ofReal (constantCoeff x) := by
  rw [IdealReconstruction.graph_iff omnificToSurreal omnificToSurreal_injective IsPurelyInfinite
    (fun x => ∃ r : ℝ, x = ofReal r) omnific_inf_iff
    (fun _ hx => hx.exists_omnific) real_iff_multiplier_and_inverse]
  constructor
  · rintro ⟨hb, hd, hm, ⟨r, hr⟩, hi⟩
    let x : nonnegativeSupportSubring.{u} :=
      ⟨omnificToSurreal a / omnificToSurreal b, (purelyInfiniteMultiplier_iff _).mp hm⟩
    have hc : r = constantCoeff x := (coefficientGraph_iff x r).mp (by rwa [hr] at hi)
    exact ⟨hb, hd, x, rfl, hr.trans (congrArg ofReal hc)⟩
  · rintro ⟨hb, hd, x, hx, hc⟩
    refine ⟨hb, hd, ?_, ⟨constantCoeff x, hc⟩, ?_⟩
    · rw [hx]
      exact (purelyInfiniteMultiplier_iff _).mpr x.property
    · rw [hx, hc]
      exact (coefficientGraph_iff x _).mpr rfl

end Foundations.SignSequence
namespace Surcomplex

/-- The Gaussian quadratic formula is exactly the actual purely infinite predicate. -/
theorem gaussianOmnific_inf_iff (x : GaussianOmnificInteger.{u}) :
    IdealReconstruction.Inf x ↔ IsPurelyInfinite (gaussianOmnificToSurcomplex x) := by
  change (∃ y : GaussianOmnificInteger, x ^ 2 = 2 * y ^ 2) ↔ IsPurelyInfinite x.val.val
  rw [isPurelyInfinite_iff, ← gaussianOmnific_purelyInfinite_iff_quadratic]
  exact CoefficientPullback.mem_ker_iff constantCoeff GaussianInt.toComplex
    GaussianInt.toComplex_injective x

/-- Every actual purely infinite surcomplex number has a Gaussian omnific representative. -/
theorem IsPurelyInfinite.exists_gaussianOmnific {z : Surcomplex.{u}} (hz : IsPurelyInfinite z) :
    ∃ w : GaussianOmnificInteger.{u}, gaussianOmnificToSurcomplex w = z := by
  let a : nonnegativeSupportSubring.{u} := ⟨z, hz.mem_supportRing⟩
  have ha : constantCoeff a = 0 := (isPurelyInfinite_iff a).mp hz
  exact ⟨⟨a, ⟨0, by rw [map_zero]; exact ha.symm⟩⟩, rfl⟩

private theorem gaussianInclusion_injective : Function.Injective gaussianOmnificToSurcomplex.{u} :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- Mult defines the actual complex support ring on Gaussian omnific fractions. -/
theorem gaussianOmnific_multiplierFormula_iff (a b : GaussianOmnificInteger.{u}) :
    IdealReconstruction.Mult a b ↔ b ≠ 0 ∧
      gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b ∈ nonnegativeSupportSubring := by
  rw [IdealReconstruction.mult_iff gaussianOmnificToSurcomplex gaussianInclusion_injective
    IsPurelyInfinite gaussianOmnific_inf_iff (fun _ hx => hx.exists_gaussianOmnific)]
  exact and_congr Iff.rfl (purelyInfiniteMultiplier_iff _)

/-- Coeff defines precisely the actual embedded complex coefficient field. -/
theorem gaussianOmnific_coefficientFormula_iff (a b : GaussianOmnificInteger.{u}) :
    IdealReconstruction.Coeff a b ↔ b ≠ 0 ∧
      ∃ c : ℂ, gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b = ofComplex c :=
  IdealReconstruction.coeff_iff gaussianOmnificToSurcomplex gaussianInclusion_injective IsPurelyInfinite
    (fun z => ∃ c : ℂ, z = ofComplex c) gaussianOmnific_inf_iff
    (fun _ hz => hz.exists_gaussianOmnific) complex_iff_multiplier_and_inverse a b

/-- The actual complex coefficient-map graph is likewise subtraction into the ideal. -/
theorem coefficientGraph_iff (z : nonnegativeSupportSubring.{u}) (c : ℂ) :
    IsPurelyInfinite (z.val - ofComplex c) ↔ c = constantCoeff z := by
  change IsPurelyInfinite (z - complexConstants c).val ↔ _
  rw [isPurelyInfinite_iff]
  change constantCoeff (z - complexConstants c) = 0 ↔ _
  rw [map_sub, constantCoeff_complexConstants, sub_eq_zero, eq_comm]

/-- The literal four-coordinate pair formula is the graph of actual coefficient extraction. -/
theorem gaussianOmnific_reconstructionGraph_iff (a b c d : GaussianOmnificInteger.{u}) :
    IdealReconstruction.Graph a b c d ↔ b ≠ 0 ∧ d ≠ 0 ∧
      ∃ x : nonnegativeSupportSubring.{u},
        gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b = x.val ∧
        gaussianOmnificToSurcomplex c / gaussianOmnificToSurcomplex d = ofComplex (constantCoeff x) := by
  rw [IdealReconstruction.graph_iff gaussianOmnificToSurcomplex gaussianInclusion_injective IsPurelyInfinite
    (fun x => ∃ r : ℂ, x = ofComplex r) gaussianOmnific_inf_iff
    (fun _ hx => hx.exists_gaussianOmnific) complex_iff_multiplier_and_inverse]
  constructor
  · rintro ⟨hb, hd, hm, ⟨r, hr⟩, hi⟩
    let x : nonnegativeSupportSubring.{u} :=
      ⟨gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b, (purelyInfiniteMultiplier_iff _).mp hm⟩
    have hc : r = constantCoeff x := (coefficientGraph_iff x r).mp (by rwa [hr] at hi)
    exact ⟨hb, hd, x, rfl, hr.trans (congrArg ofComplex hc)⟩
  · rintro ⟨hb, hd, x, hx, hc⟩
    refine ⟨hb, hd, ?_, ⟨constantCoeff x, hc⟩, ?_⟩
    · rw [hx]
      exact (purelyInfiniteMultiplier_iff _).mpr x.property
    · rw [hx, hc]
      exact (coefficientGraph_iff x _).mpr rfl

end Surcomplex
end
end Surreal
