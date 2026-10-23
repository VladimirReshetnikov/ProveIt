import BusyBeaver.ZFC.L2Control219
import BusyBeaver.ZFC.L2Axioms222

/-! The AX routine of `dag219` reuses `dag222`'s pure effect and evaluation.
Its run transfers through the equivalent equality test, as the other shared contracts do. -/

namespace SetTheory.BusyBeaver.ZFC.L2Q

open RMDag

def f236 (st : AS) : AS := L2K.f236 st

theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  trCore (n := 236) rfl (L2K.l236 st hc)

theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := L2K.c236 st hc

/-- **The AX routine is Enum222's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum222.gate a (h + (Cantor.ofNat pl).1) c,
        Enum222.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := L2K.ax_eval np t S c a h pl

end SetTheory.BusyBeaver.ZFC.L2Q
