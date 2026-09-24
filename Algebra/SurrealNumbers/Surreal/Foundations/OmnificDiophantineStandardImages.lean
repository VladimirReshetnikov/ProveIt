import Surreal.Algebra.IntegerDiophantineGuards
import Surreal.Foundations.OmnificDiophantineEnumeration
import Surreal.Surcomplex.DiophantineConstants

/-!
# Guarded Diophantine lifting to actual omnific integers

The standard-supported lifting construction in `odg:def:thm:ce` on the
actual carrier at every universe. The reverse MRDP step is separate:
this module proves exact equivalence with Diophantine definability over Z.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The finite polynomial system recognizes precisely ordinary integers in the actual omnific ring. -/
theorem omnific_diophantine_guard_iff (x : OmnificInteger.{u}) :
    IntegerDiophantine.integerGuard.Holds (fun _ => x) ↔ ∃ z : ℤ, x = (z : OmnificInteger.{u}) := by
  rw [IntegerDiophantine.holds_integerGuard_iff, omnific_xi_iff]
  have he : omnificIntCast = Int.castRingHom OmnificInteger.{u} := Subsingleton.elim _ _
  rw [he]
  rfl

/-- Every integer Diophantine presentation lifts, with guards excluding all nonstandard free tuples. -/
theorem omnific_standardImage_definable_iff {n : ℕ} (D : Set (Fin n → ℤ)) :
    IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage D : Set (Fin n → OmnificInteger.{u})) ↔
        IntegerDiophantine.Definable D :=
  IntegerDiophantine.standardImage_definable_iff omnificConstantCoeff
    IntegerDiophantine.integerGuard omnific_diophantine_guard_iff D

end
end Surreal.Foundations.SignSequence
