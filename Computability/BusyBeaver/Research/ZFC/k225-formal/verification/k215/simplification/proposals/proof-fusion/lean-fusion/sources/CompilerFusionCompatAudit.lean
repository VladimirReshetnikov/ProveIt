import BusyBeaver.ZFC.EnumPermCompat

namespace K215CompilerFusionCompatAudit
open SetTheory.BusyBeaver.ZFC
example {n : Nat} (h : KCodeDom.CDom n) : ∃ p : List EnumPerm.Cmd, EnumPerm.Contract p n :=
  EnumPerm.build h
#print axioms EnumPerm.build
end K215CompilerFusionCompatAudit
