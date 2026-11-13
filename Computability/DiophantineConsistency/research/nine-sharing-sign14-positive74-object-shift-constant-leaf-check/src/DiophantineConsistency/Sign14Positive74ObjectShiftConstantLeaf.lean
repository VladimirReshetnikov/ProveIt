import DiophantineConsistency.Sign14Positive74ObjectCompilerConstant
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRANativeAxiomImage

/-! SOURCE ONLY: native equality of actual compiled constant leaves. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftConstantLeaf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectCompilerConstant
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def constantLeaf {n : ℕ} (v w : Fin n → Term language ℕ) (k : ℕ) :
    extended nativeTheory ⊢!
      eqAt (compiledOpen (.constant k) v) (compiledOpen (.constant k) w) := by
  have hrefl : nativeTheory ⊢! eqReflI := Classical.choice
    (IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl))
  rw [← compiled_constant k v w]
  exact IPRAStandardTheory.eqReflAt hrefl (compiledOpen (.constant k) v)
end DiophantineConsistency.Sign14Positive74ObjectShiftConstantLeaf
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftConstantLeaf.constantLeaf
