import BusyBeaver.ZFC.L2Perm
import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.AXWord

/-!
The AX routine of `dagPerm` (node 236) as a checked word of register macros.

`AXWord` composes the shared native macro contracts; a kernel check binds the word to the
literal program. The final gate transfers from `dag222`, and symbolic evaluation gives
EnumPerm's AX step (`ax_eval`).
-/

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm Code254 KCode222 AXWord
open L2K (AS enc Clean ofNat_P)

attribute [local irreducible] Code254.P

set_option maxRecDepth 4096

def axWord : List AXAtom := [
  .par1, .par2, .wal, .par3, .par1, .readp2, .cons, .readp1] ++ AXWord.axBody

theorem axWord_checked : axWordCheck dagPerm 457 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := axWordEval axWord st
theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  axWordRun (fun a {_ _} h => tr (by cases a <;> rfl)
    (L2K.trCore (by cases a <;> rfl) h))
    (fun st => tr (n := 208) rfl (L2K.loop208 st))
    (fun st hc => tr (n := 457) rfl (AXWord.gate222 st hc)) axWord axWord_checked st hc
theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := axWordClean axWord st hc

/-- **The AX routine is EnumPerm's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f236, axWord, AXWord.axBody, List.cons_append, List.nil_append, axWordEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,
    EnumPerm.gate, EnumPerm.axStack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wex]

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Perm
