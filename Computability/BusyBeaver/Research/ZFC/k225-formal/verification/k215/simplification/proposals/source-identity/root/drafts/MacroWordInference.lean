import BusyBeaver.ZFC.RMDag

/-! Proposed data extractor. Soundness remains in the existing axWordCheck theorem.
This draft has not been compiled. It adds no axiom or soundness theorem. -/
namespace SetTheory.BusyBeaver.ZFC.MacroWordInference
open RMDag

def inferWord {α : Type} (nodes : Nat → Edge × Edge)
    (decode : Nat → Option α) (stop : Nat) : Nat → Nat → Option (List α)
  | 0, n => if n = stop then some [] else none
  | fuel + 1, n =>
    if n = stop then some [] else
      match nodes n with
      | (.node m, .node next) => do
        let a ← decode m
        let rest ← inferWord nodes decode stop fuel next
        pure (a :: rest)
      | _ => none

end SetTheory.BusyBeaver.ZFC.MacroWordInference
