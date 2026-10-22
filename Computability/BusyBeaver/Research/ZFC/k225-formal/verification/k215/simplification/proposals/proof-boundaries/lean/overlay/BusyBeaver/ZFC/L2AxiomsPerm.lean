import BusyBeaver.ZFC.L2Perm
import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.AXWord

/-! Literal binding of dagPerm's AX word to the shared symbolic AX proof. -/
namespace SetTheory.BusyBeaver.ZFC.L2Perm
open RMDag DagPerm
open L2K (AS enc Clean)

abbrev axWord := AXWord.axWord true
theorem axWord_checked : AXWord.axWordCheck dagPerm 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := AXWord.axWordEval axWord st

theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  AXWord.axWordRun
    (fun st hc a => tr (by cases a <;> rfl) (AXWord.AXAtom.run st hc a))
    (fun st hc => tr rfl (AXWord.l457 st hc)) axWord axWord_checked st hc

theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := AXWord.axWordClean axWord st hc

theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := AXWord.ax_eval true np t S c a h pl

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Perm
