import DiophantineConsistency.Sign14Positive74ObjectShiftBase
import DiophantineConsistency.IPRAFunctionCongruenceClosed

/-! SOURCE ONLY: instantiate native arbitrary-arity function congruence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectFunctionOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRATheoryInstantiation IPRAFunctionCongruenceClosed
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def functionOpen {k : ℕ} (f : language.Func k)
    (v : Fin (k+k) → Term language ℕ) :
    extended nativeTheory ⊢! (Rew.embSubsts v ▹ sourceBody f) :=
  instantiateTheory (T := nativeTheory) (sourceBody f) (Classical.choice (function_native f)) v
end DiophantineConsistency.Sign14Positive74ObjectFunctionOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectFunctionOpen.functionOpen
