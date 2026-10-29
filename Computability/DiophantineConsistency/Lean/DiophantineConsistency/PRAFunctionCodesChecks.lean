import DiophantineConsistency.PRAFunctionCodes

set_option autoImplicit false
namespace DiophantineConsistency.PRAFunctionCodesChecks
open List.Vector DiophantineConsistency.PRAFunctionCodes

example (n : ℕ) (v : List.Vector ℕ n) : eval (.zero n) v = 0 := rfl
example (x : ℕ) : eval .succ (x ::ᵥ nil) = x + 1 := rfl
example (x y : ℕ) : eval (.proj (1 : Fin 2)) (x ::ᵥ y ::ᵥ nil) = y := rfl
example (r x : ℕ) : eval addCore (r ::ᵥ x ::ᵥ nil) = x + r := eval_addCore r x
example : eval addCore (3 ::ᵥ 5 ::ᵥ nil) = 8 := by decide
example {n : ℕ} (c : Code n) : Primrec (eval c) := eval_primrec c
example {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Primrec f) :
    ∃ c : Code n, eval c = f := exists_code_of_primrec h

#print axioms eval_primrec'
#print axioms eval_primrec
#print axioms exists_code_of_primrec'
#print axioms exists_code_of_primrec
#print axioms eval_addCore
end DiophantineConsistency.PRAFunctionCodesChecks
