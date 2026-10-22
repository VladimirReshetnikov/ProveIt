import BusyBeaver.ZFC.L2AxiomsPerm
import BusyBeaver.ZFC.GenericMacroWord

/-! A small, production-bound effect identity behind the difference between
the maintained Perm and Dom AX words. The source-program bindings remain
separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.AXReadCons
open L2K L2Perm

/-- Reading p1 changes only p1/pl. Constructing an implication changes only
tw/ws, so these two macro effects commute without any Clean hypothesis. -/
theorem readp1_cons (st : AS) :
    AXAtom.effect .cons (AXAtom.effect .readp1 st) =
      AXAtom.effect .readp1 (AXAtom.effect .cons st) := by
  cases st
  rfl

/-- The commutation remains valid under every macro-word prefix and suffix,
and under the actual final gate used by the AX routine. -/
theorem reordered_word (pre post : List (AXAtom × Nat)) (i j : Nat) (st : AS) :
    GenericMacroWord.eval AXAtom.effect gateF
        (pre ++ (.readp1, i) :: (.cons, j) :: post) st =
      GenericMacroWord.eval AXAtom.effect gateF
        (pre ++ (.cons, i) :: (.readp1, j) :: post) st :=
  GenericMacroWord.eval_swap AXAtom.effect gateF .readp1 .cons readp1_cons pre post i j st

#print axioms readp1_cons
#print axioms reordered_word
end SetTheory.BusyBeaver.ZFC.AXReadCons
