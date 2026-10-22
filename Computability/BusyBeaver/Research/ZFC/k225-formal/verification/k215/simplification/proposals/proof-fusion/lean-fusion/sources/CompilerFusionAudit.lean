import BusyBeaver.ZFC.EnumPerm

namespace K215CompilerFusionAudit
open SetTheory.BusyBeaver.ZFC

example {n : Nat} (h : KCode222.C222 n) : ∃ p : List EnumPerm.Cmd, EnumPerm.Contract p n :=
  EnumPerm.build_c222 h

example {s : EnumPerm.St} (hpl : s.pl = 0) (hs : EnumPerm.Inv (EnumPerm.toW s)) :
    EnumPerm.HaltsFrom s ↔ KCode222.C222 Code254.F := EnumPerm.halts_iff hpl hs

#print axioms EnumPerm.build_c222
#print axioms EnumPerm.complete
#print axioms EnumPerm.halts_iff
end K215CompilerFusionAudit
