import DiophantineConsistency.Sign14Positive74ObjectCompilerOps

/-! SOURCE ONLY: conditional native equality induction for actual compiled trees. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCompilerInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectFunctionBinary
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

inductive Aligned {n : ℕ} (v w : Fin n → Term language ℕ) :
    NatExpr (Fin n) → NatExpr (Fin n) → Type where
  | leaf (p q : NatExpr (Fin n))
      (h : extended nativeTheory ⊢! eqAt (compiledOpen p v) (compiledOpen q w)) : Aligned v w p q
  | add {p p' q q'} : Aligned v w p p' → Aligned v w q q' →
      Aligned v w (.add p q) (.add p' q')
  | mul {p p' q q'} : Aligned v w p p' → Aligned v w q q' →
      Aligned v w (.mul p q) (.mul p' q')

def alignNative {n : ℕ} {v w : Fin n → Term language ℕ} :
    {p q : NatExpr (Fin n)} → Aligned v w p q →
      extended nativeTheory ⊢! eqAt (compiledOpen p v) (compiledOpen q w)
  | _, _, .leaf _ _ h => h
  | _, _, .add (p := p) (p' := p') (q := q) (q' := q') hp hq => by
      have h₁ := alignNative hp
      have h₂ := alignNative hq
      have hc : extended nativeTheory ⊢!
          (eqAt (compiledOpen p v) (compiledOpen p' w) ⋏
            (eqAt (compiledOpen q v) (compiledOpen q' w) ⋏ ⊤)) :=
        Entailment.and₃ ⨀ h₁ ⨀ (Entailment.and₃ ⨀ h₂ ⨀ Entailment.verum)
      simpa only [compiled_add] using
        (binaryOpen addCode (compiledOpen p v) (compiledOpen q v)
          (compiledOpen p' w) (compiledOpen q' w) ⨀ hc)
  | _, _, .mul (p := p) (p' := p') (q := q) (q' := q') hp hq => by
      have h₁ := alignNative hp
      have h₂ := alignNative hq
      have hc : extended nativeTheory ⊢!
          (eqAt (compiledOpen p v) (compiledOpen p' w) ⋏
            (eqAt (compiledOpen q v) (compiledOpen q' w) ⋏ ⊤)) :=
        Entailment.and₃ ⨀ h₁ ⨀ (Entailment.and₃ ⨀ h₂ ⨀ Entailment.verum)
      simpa only [compiled_mul] using
        (binaryOpen mulCode (compiledOpen p v) (compiledOpen q v)
          (compiledOpen p' w) (compiledOpen q' w) ⨀ hc)
end DiophantineConsistency.Sign14Positive74ObjectCompilerInduction
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerInduction.alignNative
