import DiophantineConsistency.Sign14Positive74ObjectFunctionBinary

/-! SOURCE ONLY: actual arithmetic-expression compiler operation shapes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCompilerOps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory FoundationHANoZero

def compiledOpen {n : ℕ} (e : NatExpr (Fin n)) (v : Fin n → Term language ℕ) : Term language ℕ :=
  Rew.embSubsts v (Semiterm.lMap embedding (sourceTerm n (ArithmeticExpression.term Fin.val e)))

theorem compiled_add {n : ℕ} (p q : NatExpr (Fin n)) (v : Fin n → Term language ℕ) :
    compiledOpen (.add p q) v = .func addCode ![compiledOpen p v, compiledOpen q v] := by
  simp [compiledOpen, ArithmeticExpression.term, sourceTerm, reflectTerm,
    Semiterm.lMap_func, Rew.func, embedding, Function.comp_def, funext_iff, Fin.forall_fin_two]

theorem compiled_mul {n : ℕ} (p q : NatExpr (Fin n)) (v : Fin n → Term language ℕ) :
    compiledOpen (.mul p q) v = .func mulCode ![compiledOpen p v, compiledOpen q v] := by
  simp [compiledOpen, ArithmeticExpression.term, sourceTerm, reflectTerm,
    Semiterm.lMap_func, Rew.func, embedding, Function.comp_def, funext_iff, Fin.forall_fin_two]
end DiophantineConsistency.Sign14Positive74ObjectCompilerOps
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerOps.compiled_add
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerOps.compiled_mul
