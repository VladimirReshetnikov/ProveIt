import Surreal.Algebra.NaturalNumbersDefinition
import Surreal.Foundations.OmnificQuintic

/-!
# Natural numbers defined inside the actual omnific integers

The full `odg:def:cor:naturals`, uniformly for every predicate defining Z.
The four-square witnesses range over the whole actual omnific ring;
requiring them to be integer constants is unnecessary.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Every definition of integer constants yields the asserted definition of natural constants. -/
theorem omnific_natural_iff_standard_four_squares (Std : OmnificInteger.{u} → Prop)
    (hStd : ∀ x, Std x ↔ ∃ a : ℤ, x = omnificIntCast a) (x : OmnificInteger.{u}) :
    (∃ n : ℕ, x = omnificIntCast n) ↔ Std x ∧
      ∃ s : Fin 4 → OmnificInteger.{u}, x = ∑ j, s j ^ 2 := by
  have hi (a : ℤ) : omnificIntCast.{u} a = (a : OmnificInteger.{u}) :=
    map_intCast omnificIntCast a
  have hStd' : ∀ x, Std x ↔ ∃ a : ℤ, x = (a : OmnificInteger.{u}) := by
    simpa only [hi] using hStd
  simpa only [hi, Int.cast_natCast] using
    NaturalNumbersDefinition.natural_iff_standard_four_squares Std hStd' x

/-- Instantiation with the order-free three-equation predicate. -/
theorem omnific_natural_iff_xi_four_squares (x : OmnificInteger.{u}) :
    (∃ n : ℕ, x = omnificIntCast n) ↔ DiophantineConstants.Xi x ∧
      ∃ s : Fin 4 → OmnificInteger.{u}, x = ∑ j, s j ^ 2 :=
  omnific_natural_iff_standard_four_squares _ omnific_xi_iff x

/-- Instantiation with the seven-witness real quintic. -/
theorem omnific_natural_iff_quintic_four_squares (x : OmnificInteger.{u}) :
    (∃ n : ℕ, x = omnificIntCast n) ↔ QuinticConstants.Defines x ∧
      ∃ s : Fin 4 → OmnificInteger.{u}, x = ∑ j, s j ^ 2 :=
  omnific_natural_iff_standard_four_squares _ omnific_quintic_iff x

end
end Surreal.Foundations.SignSequence
