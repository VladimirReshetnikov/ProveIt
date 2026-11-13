import DiophantineConsistency.Sign14Positive74ObjectCompilerInduction

/-! SOURCE ONLY: shift-specific native term induction with explicit leaf proofs. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectPredecessor AdaptiveEquationSyntax2011
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectCompilerInduction
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def splitTrees {n : ℕ} (v w : Fin n → Term language ℕ)
    (hconst : ∀ k : ℕ, extended nativeTheory ⊢!
      eqAt (compiledOpen (.constant k) v) (compiledOpen (.constant k) w))
    (hpos : ∀ i : Fin n, extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.var i) (.constant 1)) v) (compiledOpen (.var i) w))
    (hneg : extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.constant 0) (.constant 0)) v) (compiledOpen (.constant 0) w))
    (e : Expr (Fin n)) :
    Aligned v w (positiveShift e).splitNatural.1 e.splitNatural.1 ×
      Aligned v w (positiveShift e).splitNatural.2 e.splitNatural.2 := by
  induction e with
  | constant z => exact ⟨.leaf _ _ (hconst _), .leaf _ _ (hconst _)⟩
  | var i => exact ⟨.leaf _ _ (hpos i), .leaf _ _ hneg⟩
  | add p q hp hq => exact ⟨.add hp.1 hq.1, .add hp.2 hq.2⟩
  | sub p q hp hq => exact ⟨.add hp.1 hq.2, .add hp.2 hq.1⟩
  | mul p q hp hq =>
      exact ⟨.add (.mul hp.1 hq.1) (.mul hp.2 hq.2),
        .add (.mul hp.1 hq.2) (.mul hp.2 hq.1)⟩

def splitNative {n : ℕ} (v w : Fin n → Term language ℕ)
    (hconst : ∀ k : ℕ, extended nativeTheory ⊢!
      eqAt (compiledOpen (.constant k) v) (compiledOpen (.constant k) w))
    (hpos : ∀ i : Fin n, extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.var i) (.constant 1)) v) (compiledOpen (.var i) w))
    (hneg : extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.constant 0) (.constant 0)) v) (compiledOpen (.constant 0) w))
    (e : Expr (Fin n)) :
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.1 v) (compiledOpen e.splitNatural.1 w)) ×
    (extended nativeTheory ⊢!
      eqAt (compiledOpen (positiveShift e).splitNatural.2 v) (compiledOpen e.splitNatural.2 w)) :=
  ⟨alignNative (splitTrees v w hconst hpos hneg e).1,
    alignNative (splitTrees v w hconst hpos hneg e).2⟩
end DiophantineConsistency.Sign14Positive74ObjectShiftInduction
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftInduction.splitTrees
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftInduction.splitNative
