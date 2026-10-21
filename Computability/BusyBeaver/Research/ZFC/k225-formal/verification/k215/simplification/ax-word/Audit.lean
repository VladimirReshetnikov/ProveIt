import BusyBeaver.ZFC.L2AxiomsPerm

namespace SetTheory.BusyBeaver.ZFC.L2Perm
open L2K (AS Clean)

example (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) := l236 st hc
example (st : AS) (hc : Clean st) : Clean (f236 st) := c236 st hc
example (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1)
          (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h
          (h + (Cantor.ofNat pl).1) c a t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ :=
  ax_eval np t S c a h pl

#print axioms l236
#print axioms c236
#print axioms ax_eval

end SetTheory.BusyBeaver.ZFC.L2Perm
