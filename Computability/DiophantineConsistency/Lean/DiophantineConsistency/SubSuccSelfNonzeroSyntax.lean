import DiophantineConsistency.PRATheory

/-! The terms shared by the classical and intuitionistic successor-subtraction statements. -/

set_option autoImplicit false

namespace DiophantineConsistency.SubSuccSelfNonzeroSyntax

open LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes (Code)
open PRATheory (TermN subCode)

def term : TermN 1 := .func subCode ![.func Code.succ (fun _ => #0), #0]
def zero : TermN 1 := .func (.zero 0) Fin.elim0

end DiophantineConsistency.SubSuccSelfNonzeroSyntax
