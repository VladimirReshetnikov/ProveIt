import DiophantineConsistency.PRALanguage

/-! Terms shared by induction conversion and the difference argument.
The original namespaces keep the public term names used by existing proofs. -/
set_option autoImplicit false

namespace DiophantineConsistency

open LO.FirstOrder

namespace IPRADifferenceSuccEq
open PRALanguage PRAFiniteFunctionCodes

def sx (x : Term language ℕ) : Term language ℕ := .func Code.succ (fun _ => x)

end IPRADifferenceSuccEq

namespace IPRADifferenceStepClosure
open PRALanguage

def addOneTerm (x : Term language ℕ) : Term language ℕ := .func addCode ![x, .func oneCode Fin.elim0]

end IPRADifferenceStepClosure
end DiophantineConsistency
