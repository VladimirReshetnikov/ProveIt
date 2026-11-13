import DiophantineConsistency.Sign14Positive74ObjectShiftInduction

/-! SOURCE ONLY: leaf shapes in the actual arithmetic compiler. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory FoundationHANoZero
open Sign14Positive74ObjectPredecessor Sign14Positive74ObjectCompilerOps

def one : Term language ℕ := .func oneCode Fin.elim0

theorem compiled_var {n : ℕ} (i : Fin n) (v : Fin n → Term language ℕ) :
    compiledOpen (.var i) v = v i := by
  simp [compiledOpen, ArithmeticExpression.term, sourceTerm, reflectTerm, slot,
    Semiterm.lMap_bvar, Rew.embSubsts, i.isLt]

theorem compiled_zero {n : ℕ} (v : Fin n → Term language ℕ) :
    compiledOpen (.constant 0) v = zero := by
  simp [compiledOpen, ArithmeticExpression.term, ArithmeticExpression.binaryNumeral,
    sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func, embedding, zero]

theorem compiled_one {n : ℕ} (v : Fin n → Term language ℕ) :
    compiledOpen (.constant 1) v =
      .func addCode ![.func mulCode ![.func addCode ![.func addCode ![zero,one],one],zero],one] := by
  simp [compiledOpen, ArithmeticExpression.term, ArithmeticExpression.binaryNumeral,
    sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func, embedding, zero, one,
    Function.comp_def, funext_iff, Fin.forall_fin_two] <;> rfl
end DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves.compiled_var
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves.compiled_zero
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves.compiled_one
