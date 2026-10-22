import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.KCodeDom

/-!
Compatibility import for clients using the former `EnumPerm.build` theorem.
Import this module instead of `EnumPerm` when the CDom-specific API is required.
The active K215 endpoint does not import this adapter.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

/-- The former compiler interface, now an adapter to direct C222 compilation. -/
theorem build : ∀ {n : Nat}, KCodeDom.CDom n → ∃ p : List Cmd, Contract p n :=
  fun h => build_c222 (KCodeDom.c222_of_cdom h)

end SetTheory.BusyBeaver.ZFC.EnumPerm
