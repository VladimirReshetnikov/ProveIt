module
public import PA196.CheckCoverage
@[expose] public section
namespace PA196.Arithmetic.Machine.OriginalCheck
abbrev path := PA196.Program.path
def frame (p : M6.Source.Path) (extra : Nat := 0) (e : M6.Runtime.Eff := .none) : M6.Runtime.SConf :=
  PA196.RuntimeContracts.rootFrame p extra e
abbrev codeAt := PA196.CheckCoverage.codeAt
abbrev checkInstruction := PA196.CheckCoverage.checkInstruction
abbrev checkAt := PA196.CheckCoverage.checkAt
abbrev blockCheck := PA196.CheckCoverage.blockCheck
end PA196.Arithmetic.Machine.OriginalCheck
