import DiophantineConsistency.Sign14Positive74ObjectEqualityTransport

/-! SOURCE ONLY: actual shifted equality-matrix transport. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftMatrix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability AdaptiveEquationSyntax2011
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectMatrixGuard
open Sign14Positive74ObjectShiftPositiveLeaf Sign14Positive74ObjectShiftFull Sign14Positive74ObjectEqualityTransport
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem matrixOpen (e : Expr (Fin 14)) (v : Fin 14 → Term language ℕ) :
    (Rew.embSubsts v ▹ equalityMatrix e) =
      eqAt (compiledOpen e.splitNatural.1 v) (compiledOpen e.splitNatural.2 v) := by
  unfold equalityMatrix eqAt
  rw [Semiformulaᵢ.rew_rel]
  congr 1
  funext i
  fin_cases i <;> rfl

def shiftForward (v : Fin 14 → Term language ℕ) (e : Expr (Fin 14)) :
    extended nativeTheory ⊢!
      ((Rew.embSubsts v ▹ equalityMatrix (positiveShift e)) 🡒
        (Rew.embSubsts (succVec v) ▹ equalityMatrix e)) := by
  have h := shiftFull v e
  rw [matrixOpen, matrixOpen]
  exact equalityForward _ _ _ _ h.1 h.2

def shiftBackward (v : Fin 14 → Term language ℕ) (e : Expr (Fin 14)) :
    extended nativeTheory ⊢!
      ((Rew.embSubsts (succVec v) ▹ equalityMatrix e) 🡒
        (Rew.embSubsts v ▹ equalityMatrix (positiveShift e))) := by
  have h := shiftFull v e
  rw [matrixOpen, matrixOpen]
  exact equalityBackward _ _ _ _ h.1 h.2
end DiophantineConsistency.Sign14Positive74ObjectShiftMatrix
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftMatrix.matrixOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftMatrix.shiftForward
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftMatrix.shiftBackward
