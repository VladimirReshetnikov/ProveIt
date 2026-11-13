import DiophantineConsistency.IPRAReferenceAddOne
import DiophantineConsistency.IPRAErasedInductionShape
import DiophantineConsistency.IPRAReferencePredecessor

/-! Exploratory open instantiation of the reference addition-one image. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceAddOneOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAErasedDefiningImages
open IPRAEqualityOnlyReference IPRAReferenceEqualityTools IPRAReferencePredecessor
open IPRATheoryHilbertBridge IPRATheoryInstantiation

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

def one : Term language ℕ := .func PRALanguage.oneCode Fin.elim0
def addOne (x : Term language ℕ) : Term language ℕ := .func PRALanguage.addCode ![x,one]
def body : Semisentenceᵢ language 1 := .rel EqualityRel.eq
  ![IPRAErasedInductionShape.stepTerm 0, .func .succ (fun _ => #0)]

theorem erase_addOne : erase IPRAAddOneDirect.addOneI = ∀⁰* body := by
  simp only [IPRAAddOneDirect.addOneI, IPRANativeInduction.stepTerm, PRATheory.applyCode,
    erase, body, IPRAErasedInductionShape.stepTerm]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Semiterm.lMap_func, termsToReference, Function.comp_def]
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
      simp [Semiterm.lMap_func]
      funext k
      exact Fin.elim0 k
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [Semiterm.lMap_func, termsToReference, Function.comp_def]

def addOneOpen (x : Term language ℕ) : extended referenceTheory ⊢! eqAt (addOne x) (succ x) := by
  have ha : referenceTheory ⊢! ∀⁰* body := by
    rw [← erase_addOne]
    exact Classical.choice IPRAReferenceAddOne.addOne_image
  have hp := instantiateTheory (T := referenceTheory) body ha ![x]
  convert hp using 1
  simp [body, eqAt, addOne, one, succ, IPRAErasedInductionShape.stepTerm, Semiformulaᵢ.rew_rel]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Rew.func, Function.comp_def]
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
      simp [Rew.func, Function.comp_def]
      funext k
      exact Fin.elim0 k
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [Rew.func, Function.comp_def]

end DiophantineConsistency.IPRAReferenceAddOneOpen
