import DiophantineConsistency.PRALanguage

set_option autoImplicit false
namespace DiophantineConsistency.PRALanguageChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage List.Vector

example : language.Encodable := inferInstance
example : embedding.func Language.ORing.Func.zero = Code.zero 0 := rfl
example : embedding.func Language.ORing.Func.one = oneCode := rfl
example : embedding.func Language.ORing.Func.add = addCode := rfl
example : embedding.func Language.ORing.Func.mul = mulCode := rfl
example : embedding.rel Language.ORing.Rel.eq = Language.ORing.Rel.eq := rfl
example : embedding.rel Language.ORing.Rel.lt = Language.ORing.Rel.lt := rfl
example (x y : ℕ) : eval addCode (x ::ᵥ y ::ᵥ nil) = x+y := eval_addCode x y
example (x y : ℕ) : eval mulCode (x ::ᵥ y ::ᵥ nil) = x*y := eval_mulCode x y
example {n : ℕ} (f : language.Func n) : Primrec (eval f) := eval_primrec f
example {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (b : Fin n → ℕ) (v : ξ → ℕ) :
    Semiformula.Eval (s := natStructure) b v (Semiformula.lMap embedding φ) ↔
      Semiformula.Eval (s := Arithmetic.standardModel ℕ) b v φ := nat_formula_map φ b v

#print axioms eval_addCode
#print axioms eval_mulCode
#print axioms nat_reduct
#print axioms nat_formula_map
end DiophantineConsistency.PRALanguageChecks
