import DiophantineConsistency.Sign14Positive74ObjectNumeralOne
import DiophantineConsistency.IPRAAddOneDirect
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRANativeAxiomImage

/-! SOURCE ONLY: actual compiled positive-variable leaf. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftPositiveLeaf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeInduction
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
open Sign14Positive74ObjectCompilerOps Sign14Positive74ObjectCompilerLeaves
open Sign14Positive74ObjectFunctionBinary Sign14Positive74ObjectNumeralTools Sign14Positive74ObjectNumeralOne
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def addOneOpen (x : Term language ℕ) : extended nativeTheory ⊢!
    eqAt (.func addCode ![x, .func oneCode Fin.elim0]) (.func .succ (fun _ => x)) := by
  let m : Semisentenceᵢ language 1 :=
    Semiformulaᵢ.rel .eq ![.func addCode ![#0, .func oneCode Fin.elim0],
      .func .succ (fun _ => #0)]
  have ha : nativeTheory ⊢! ∀⁰* m := by
    apply Classical.choice
    simpa [m, IPRAAddOneDirect.addOneI, stepTerm, applyCode, allClosure_succ,
      Entailment.Provable] using IPRAAddOneDirect.add_one_native
  have hp := instantiateTheory (T := nativeTheory) m ha ![x]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![x])
      (![.func addCode ![#0, .func oneCode Fin.elim0], .func .succ (fun _ => #0)] i)) =
        ![.func addCode ![x, .func oneCode Fin.elim0], .func .succ (fun _ => x)] := by
    apply funext
    simp [Fin.forall_fin_two, Rew.func, funext_iff]
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def succVec {n : ℕ} (v : Fin n → Term language ℕ) : Fin n → Term language ℕ :=
  fun i => .func .succ (fun _ => v i)

def positiveLeaf {n : ℕ} (v : Fin n → Term language ℕ) (i : Fin n) :
    extended nativeTheory ⊢!
      eqAt (compiledOpen (.add (.var i) (.constant 1)) v) (compiledOpen (.var i) (succVec v)) := by
  let o := Sign14Positive74ObjectCompilerLeaves.one
  let t := compiledOpen (.constant 1) v
  have hr : nativeTheory ⊢! eqReflI := Classical.choice
    (IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl))
  have hv : extended nativeTheory ⊢! eqAt (v i) (v i) := IPRAStandardTheory.eqReflAt hr (v i)
  have ho : extended nativeTheory ⊢! eqAt t o := oneNormalize v
  have hc : extended nativeTheory ⊢! (eqAt (v i) (v i) ⋏ (eqAt t o ⋏ ⊤)) :=
    Entailment.and₃ ⨀ hv ⨀ (Entailment.and₃ ⨀ ho ⨀ Entailment.verum)
  have hstep : extended nativeTheory ⊢!
      eqAt (.func addCode ![v i,t]) (.func addCode ![v i,o]) :=
    binaryOpen addCode (v i) t (v i) o ⨀ hc
  have hfinal := transOpen (.func addCode ![v i,t]) (.func addCode ![v i,o])
    (.func .succ (fun _ => v i)) ⨀ hstep ⨀ addOneOpen (v i)
  simpa only [compiled_add, compiled_var, succVec, t, o] using hfinal
end DiophantineConsistency.Sign14Positive74ObjectShiftPositiveLeaf
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftPositiveLeaf.positiveLeaf
