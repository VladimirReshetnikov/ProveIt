import DiophantineConsistency.ScalarPRCode
import Mathlib.Computability.Primrec.List

/-!
This is the bridge needed to reverse the Computability / DirectScalarEnumerator
import dependency. It is proved against the exact current ScalarPRCode source.
It does not assert that the complete source split has been rebuilt.
-/

namespace DiophantineConsistency.ScalarPRCode.Realizes

theorem natPrimrec {f : ℕ → ℕ} (p : Realizes f) : Nat.Primrec f :=
  p.val.primrec.of_eq p.property

theorem vectorPrimrec {f : ℕ → ℕ} (p : Realizes f) :
    Nat.Primrec' (fun v : List.Vector ℕ 1 => f v.head) :=
  Nat.Primrec'.prim_iff₁.mpr (Primrec.nat_iff.mpr p.natPrimrec)

#print axioms natPrimrec
#print axioms vectorPrimrec

end DiophantineConsistency.ScalarPRCode.Realizes
