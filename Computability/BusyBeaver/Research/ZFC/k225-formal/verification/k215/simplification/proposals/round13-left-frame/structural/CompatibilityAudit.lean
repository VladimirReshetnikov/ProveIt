import BusyBeaver.ZFC.EnumDom
import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.L2RootPerm
import BusyBeaver.ZFC.SeedDom
import BusyBeaver.ZFC.SeedPerm

/- Source-only adoption gate; NOT compiled in this review.
   Compile after rebuilding both enumerators and every imported consumer.
   These fully qualified references exercise namespace-export compatibility,
   not just equality of copied declaration text. -/
namespace SetTheory.BusyBeaver.ZFC.StructuralCompatibilityAudit
open Code254 KCode222

example (z : Nat) : EnumDom.unP z = EnumPerm.unP z := rfl
example (a b c : Nat) : EnumDom.gate a b c = EnumPerm.gate a b c := rfl
example (k z : Nat) : EnumDom.tailN k z = EnumPerm.tailN k z := rfl
example (z : Nat) : EnumDom.Good z ↔ EnumPerm.Good z := Iff.rfl
example (a h b c u t w : Nat) :
    EnumDom.axStack a h b c u t w = EnumPerm.axStack a h b c u t w := rfl

-- `unfold` and simplifier references must also resolve the exported aliases.
example (a b : Nat) : EnumDom.gate a b a = 0 := by
  unfold EnumDom.gate
  simp
example (k z : Nat) : EnumPerm.tailN (k + 1) z =
    EnumPerm.tailN k (EnumPerm.unP z).2 := by
  simp only [EnumPerm.tailN]
example (x z : Nat) (hx : C222 x) (hz : EnumDom.Good z) :
    EnumPerm.Good (P x z) := EnumDom.good_cons hx hz
example (a h b c u t w : Nat) :
    EnumDom.axStack a h b c u t w =
      P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c)
        (P (rho5 a b c) (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u)
          (P (wal u h) (P t w))))))))) := by
  unfold EnumDom.axStack
  rfl

#check EnumDom.unP_P'
#check EnumPerm.unP_P'
#check EnumDom.axStack_good
#check EnumPerm.axStack_good
#check EnumDom.halts_iff
#check EnumPerm.halts_iff
#print axioms EnumDom.halts_iff
#print axioms EnumPerm.halts_iff

end SetTheory.BusyBeaver.ZFC.StructuralCompatibilityAudit
