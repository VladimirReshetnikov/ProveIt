import DiophantineConsistency.Sign14Positive74ObjectCompilerLeaves

/-! SOURCE ONLY: actual compiled shift-negative variable leaf. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftNegativeLeaf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectCompilerLeaves
open Sign14Positive74ObjectShiftBase
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def negativeLeaf {n : ℕ} (v w : Fin n → Term language ℕ) : extended nativeTheory ⊢!
    eqAt (compiledOpen (.add (.constant 0) (.constant 0)) v) (compiledOpen (.constant 0) w) := by
  simpa only [compiled_add, compiled_zero] using zeroAddZero
end DiophantineConsistency.Sign14Positive74ObjectShiftNegativeLeaf
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftNegativeLeaf.negativeLeaf
