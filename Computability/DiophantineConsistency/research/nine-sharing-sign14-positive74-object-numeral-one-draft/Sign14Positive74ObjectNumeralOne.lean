import DiophantineConsistency.Sign14Positive74ObjectNumeralTools
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRANativeAxiomImage

/-! SOURCE ONLY: normalize the actual compiler's binary numeral one in nativeTheory. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectNumeralOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectCompilerLeaves
open Sign14Positive74ObjectFunctionBinary Sign14Positive74ObjectMulZeroContext
open Sign14Positive74ObjectMulZeroNative Sign14Positive74ObjectNumeralTools
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def oneNormalize {n : ℕ} (v : Fin n → Term language ℕ) : extended nativeTheory ⊢!
    eqAt (compiledOpen (.constant 1) v) Sign14Positive74ObjectCompilerLeaves.one := by
  let o := Sign14Positive74ObjectCompilerLeaves.one
  let two : Term language ℕ := .func addCode ![.func addCode ![zero,o],o]
  let t : Term language ℕ := .func mulCode ![two,zero]
  have hmul : extended nativeTheory ⊢! eqAt t zero := by
    simpa [t, mult, mz, zero, IPRAFunctionCongruenceOpen.equal, eqAt] using mulZeroOpen two
  have hr : nativeTheory ⊢! eqReflI := Classical.choice
    (IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl))
  have ho : extended nativeTheory ⊢! eqAt o o := IPRAStandardTheory.eqReflAt hr o
  have hc : extended nativeTheory ⊢! (eqAt t zero ⋏ (eqAt o o ⋏ ⊤)) :=
    Entailment.and₃ ⨀ hmul ⨀ (Entailment.and₃ ⨀ ho ⨀ Entailment.verum)
  have hstep : extended nativeTheory ⊢! eqAt (.func addCode ![t,o]) (.func addCode ![zero,o]) :=
    binaryOpen addCode t o zero o ⨀ hc
  have hfinal := transOpen (.func addCode ![t,o]) (.func addCode ![zero,o]) o ⨀ hstep ⨀ zeroLeftOpen o
  simpa only [compiled_one, t, two, o] using hfinal
end DiophantineConsistency.Sign14Positive74ObjectNumeralOne
#print axioms DiophantineConsistency.Sign14Positive74ObjectNumeralOne.oneNormalize
