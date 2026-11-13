import DiophantineConsistency.Sign14Positive74ObjectShiftConstantLeaf

/-! SOURCE ONLY: shift induction with the constant and negative leaves supplied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftPartial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectCompilerOps
open Sign14Positive74ObjectShiftInduction Sign14Positive74ObjectShiftNegativeLeaf
open Sign14Positive74ObjectShiftConstantLeaf AdaptiveEquationSyntax2011
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def partialSplitNative {n : ℕ} (v w : Fin n → Term language ℕ)
    (hpos : ∀ i : Fin n, extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.var i) (.constant 1)) v) (compiledOpen (.var i) w))
    (e : Expr (Fin n)) :
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.1 v) (compiledOpen e.splitNatural.1 w)) ×
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.2 v) (compiledOpen e.splitNatural.2 w)) :=
  splitNative v w (constantLeaf v w) hpos (negativeLeaf v w) e
end DiophantineConsistency.Sign14Positive74ObjectShiftPartial
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftPartial.partialSplitNative
