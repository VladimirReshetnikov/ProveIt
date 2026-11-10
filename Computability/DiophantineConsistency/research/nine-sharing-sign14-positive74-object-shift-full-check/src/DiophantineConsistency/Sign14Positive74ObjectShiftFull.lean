import DiophantineConsistency.Sign14Positive74ObjectShiftPositiveLeaf

/-! SOURCE ONLY: native compiled shift alignment for both split terms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftFull
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability AdaptiveEquationSyntax2011
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectShiftPartial
open Sign14Positive74ObjectShiftPositiveLeaf
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def shiftFull {n : ℕ} (v : Fin n → Term language ℕ) (e : Expr (Fin n)) :
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.1 v) (compiledOpen e.splitNatural.1 (succVec v))) ×
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.2 v) (compiledOpen e.splitNatural.2 (succVec v))) :=
  partialSplitNative v (succVec v) (positiveLeaf v) e
end DiophantineConsistency.Sign14Positive74ObjectShiftFull
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftFull.shiftFull
