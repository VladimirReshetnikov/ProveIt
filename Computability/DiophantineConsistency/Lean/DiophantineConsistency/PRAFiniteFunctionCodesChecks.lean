import DiophantineConsistency.PRAFiniteFunctionCodes

set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteFunctionCodesChecks
open List.Vector PRAFiniteFunctionCodes

example {n : ℕ} (c d : Code n) : Decidable (c = d) := inferInstance
example : Code.zero 1 ≠ Code.succ := by decide
example (x : ℕ) : eval Code.succ (x ::ᵥ nil) = x + 1 := rfl
example (x : ℕ) : eval (Code.comp Code.succ (.cons (.proj 0) (.nil 1)))
    (x ::ᵥ nil) = x + 1 := rfl
example {n : ℕ} (c : Code n) : Primrec (eval c) := eval_primrec c
example {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Primrec f) :
    ∃ c : Code n, eval c = f := exists_code_of_primrec h

#print axioms forgetMany_pack
#print axioms forget_surjective
#print axioms eval_primrec
#print axioms exists_code_of_primrec
end DiophantineConsistency.PRAFiniteFunctionCodesChecks
