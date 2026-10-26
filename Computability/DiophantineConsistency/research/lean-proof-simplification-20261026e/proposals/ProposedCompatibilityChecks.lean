import ProposedSharedTail
import ProposedDivModCert
import DiophantineConsistency.SplitNinePolynomial59
import DiophantineConsistency.GapNinePolynomial66
import DiophantineConsistency.QuadraticDivMod
import DiophantineConsistency.RegisterDivMod

/-! UNCOMPILED proposed compatibility checks; run in the pinned Lake context.
These show intended local compatibility, not equality of complete circuits.
-/
namespace DiophantineConsistency.ProposedCompatibilityChecks
variable {A : Type*} [CommRing A]

example (R N b g t h s w C i j n : A) :
    SplitNinePolynomial59.ratioValue R N b g t h s w C i j n =
      ProposedSharedTail.ratioValue R N b g t h s w C i j n := rfl

example (R N b g t h s w C i j n : A) :
    GapNinePolynomial66.ratioValue R N b g t h s w C i j n =
      ProposedSharedTail.ratioValue R N b g t h s w C i j n := rfl

example (q r n b : ℕ) :
    (∃ s, n = q * b + r ∧ b = r + s + 1) ↔
      0 < b ∧ q = n / b ∧ r = n % b :=
  ProposedDivModCert.correct_iff q r n b

example : QuadraticDivMod.representation.witnessCount = 1 := rfl
example : RegisterDivMod.representation.witnessCount = 23 := rfl

end DiophantineConsistency.ProposedCompatibilityChecks
