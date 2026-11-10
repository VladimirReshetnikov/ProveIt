import DiophantineConsistency.Sign14Positive74ObjectFunctionOpen

/-! SOURCE ONLY: normalize generic function congruence at arity two. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectFunctionBinary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability IPRAFunctionCongruenceOpen IPRAFunctionCongruenceClosed
open Sign14Positive74ObjectPredecessor Sign14Positive74ObjectFunctionOpen
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem binary_body (f : language.Func 2) (a b c d : Term language ℕ) :
    (Rew.embSubsts ![a,b,c,d] ▹ sourceBody f) =
      ((eqAt a c ⋏ (eqAt b d ⋏ ⊤)) 🡒
        eqAt (.func f ![a,b]) (.func f ![c,d])) := by
  simp [sourceBody, rew_matrix_conj, Matrix.conj, Matrix.vecTail, eqAt,
    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rew.func, Function.comp_def]
  constructor
  · constructor <;> funext i <;> fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp [Rew.func, Function.comp_def, funext_iff, Fin.forall_fin_two]

def binaryOpen (f : language.Func 2) (a b c d : Term language ℕ) :
    extended nativeTheory ⊢!
      ((eqAt a c ⋏ (eqAt b d ⋏ ⊤)) 🡒
        eqAt (.func f ![a,b]) (.func f ![c,d])) := by
  rw [← binary_body f a b c d]
  exact functionOpen f ![a,b,c,d]
end DiophantineConsistency.Sign14Positive74ObjectFunctionBinary
#print axioms DiophantineConsistency.Sign14Positive74ObjectFunctionBinary.binary_body
#print axioms DiophantineConsistency.Sign14Positive74ObjectFunctionBinary.binaryOpen
