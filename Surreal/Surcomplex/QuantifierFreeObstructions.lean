import Surreal.Algebra.QuantifierFreeRetraction
import Surreal.Algebra.ArithmeticGuards
import Surreal.Surcomplex.DiophantineConstantsBoundary

/-!
# Quantifier-free lower bounds on the actual omnific rings

The actual real and Gaussian versions of `odg:def:prop:notqf`.
The ideal and the ordinary coefficient image have no quantifier-free
unary definition even with all ring elements available as parameters.
The explicit Xi formula witnesses failure of quantifier elimination.
-/

universe u
namespace Surreal
open FirstOrder FirstOrder.Language
noncomputable section

namespace Foundations.SignSequence
local instance quantifierFreeOmnificStructure : FirstOrder.Ring.CompatibleRing OmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing OmnificInteger

/-- The actual purely infinite ideal cannot be defined without quantifiers, even with arbitrary parameters. -/
theorem omnific_ideal_not_quantifierFreeDefinable :
    ¬ QuantifierFree.Definable₁ (id : OmnificInteger.{u} → _) (omnificPurelyInfiniteIdeal : Set _) :=
  QuantifierFree.kernel_not_definable₁ omnificConstantCoeff
    (omnificMonomial_ne_zero 1 zero_lt_one) (omnificMonomial_mem_purelyInfinite 1 zero_lt_one) id

/-- The ordinary integers have the same quantifier-free obstruction. -/
theorem omnific_constants_not_quantifierFreeDefinable :
    ¬ QuantifierFree.Definable₁ (id : OmnificInteger.{u} → _) (Set.range omnificIntCast) :=
  QuantifierFree.constants_not_definable₁ omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast (omnificMonomial_ne_zero 1 zero_lt_one)
    (omnificMonomial_mem_purelyInfinite 1 zero_lt_one) id

/-- Xi is a concrete formula with no quantifier-free equivalent in the complete omnific theory. -/
theorem omnific_no_quantifierFree_equivalent :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory OmnificInteger.{u} ⊨ᵇ ArithmeticGuards.integerGuard.iff ψ := by
  apply QuantifierFree.no_quantifierFree_equivalent_in_completeTheory
    (RetractionInfiniteSets.constants_infinite omnificConstantCoeff omnificIntCast
      omnificConstantCoeff_intCast)
    (RetractionInfiniteSets.constants_complement_infinite omnificConstantCoeff omnificIntCast
      omnificConstantCoeff_intCast (omnificMonomial_ne_zero (1 : SignSequence.{u}) zero_lt_one)
      (omnificMonomial_mem_purelyInfinite 1 zero_lt_one))
  intro x
  rw [ArithmeticGuards.realize_integerGuard, omnific_xi_iff]
  exact exists_congr fun _ => eq_comm

end Foundations.SignSequence
namespace Surcomplex
local instance quantifierFreeGaussianStructure : FirstOrder.Ring.CompatibleRing GaussianOmnificInteger.{u} :=
  FirstOrder.Ring.compatibleRingOfRing GaussianOmnificInteger

/-- The actual Gaussian purely infinite ideal cannot be defined without quantifiers. -/
theorem gaussianOmnific_ideal_not_quantifierFreeDefinable :
    ¬ QuantifierFree.Definable₁ (id : GaussianOmnificInteger.{u} → _)
      {x | gaussianOmnificConstantCoeff x = 0} :=
  QuantifierFree.kernel_not_definable₁ gaussianOmnificConstantCoeff
    gaussianOmnificOmega_ne_zero gaussianOmnificOmega_constantCoeff id

/-- Even all Gaussian omnific parameters cannot yield a quantifier-free definition of Z[i]. -/
theorem gaussianOmnific_constants_not_quantifierFreeDefinable :
    ¬ QuantifierFree.Definable₁ (id : GaussianOmnificInteger.{u} → _) (Set.range gaussianOmnificConstants) :=
  QuantifierFree.constants_not_definable₁ gaussianOmnificConstantCoeff gaussianOmnificConstants
    gaussianOmnificConstantCoeff_constants gaussianOmnificOmega_ne_zero gaussianOmnificOmega_constantCoeff id

/-- Xi also witnesses failure of quantifier elimination for the actual Gaussian omnific theory. -/
theorem gaussianOmnific_no_quantifierFree_equivalent :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory GaussianOmnificInteger.{u} ⊨ᵇ ArithmeticGuards.integerGuard.iff ψ := by
  apply QuantifierFree.no_quantifierFree_equivalent_in_completeTheory
    (RetractionInfiniteSets.constants_infinite gaussianOmnificConstantCoeff gaussianOmnificConstants
      gaussianOmnificConstantCoeff_constants)
    (RetractionInfiniteSets.constants_complement_infinite gaussianOmnificConstantCoeff gaussianOmnificConstants
      gaussianOmnificConstantCoeff_constants gaussianOmnificOmega_ne_zero gaussianOmnificOmega_constantCoeff)
  intro x
  rw [ArithmeticGuards.realize_integerGuard, gaussianOmnific_xi_iff]
  exact exists_congr fun _ => eq_comm

end Surcomplex
end
end Surreal
