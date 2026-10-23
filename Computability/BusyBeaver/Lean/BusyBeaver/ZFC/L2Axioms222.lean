import BusyBeaver.ZFC.L2Control222
import BusyBeaver.ZFC.Enum222
import BusyBeaver.ZFC.AXWord

/-!
The AX routine of `dag222` (node 236) as a checked word of register macros.
`AXWord` composes the shared native macro contracts; a kernel check binds the word to the
literal program, including the two-node literal read. Symbolic evaluation gives `ax_eval`.
-/

namespace SetTheory.BusyBeaver.ZFC.L2K

open RMDag Dag222 Code254 KCode222 AXWord

attribute [local irreducible] Code254.P

set_option maxRecDepth 4096

def axWord : List AXAtom :=
  [.par1, .par2, .wal, .readp2, .par3, .push, .readwff, .cons] ++ AXWord.axBody

theorem axWord_checked : axWordCheck dag222 457 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := axWordEval axWord st

theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  axWordRun (fun a {_ _} h => trCore (by cases a <;> rfl) h) loop208 gate222 axWord axWord_checked st hc

theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := axWordClean axWord st hc

/-- **The AX routine is Enum222's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum222.gate a (h + (Cantor.ofNat pl).1) c,
        Enum222.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f236, axWord, AXWord.axBody, List.cons_append, List.nil_append, axWordEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,
    Enum222.gate, Enum222.axStack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wex, Nat.zero_add]

end SetTheory.BusyBeaver.ZFC.L2K
