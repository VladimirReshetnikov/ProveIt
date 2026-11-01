import DiophantineConsistency.IPRAReferenceAddOneOpen
import DiophantineConsistency.IPRAErasedInductionObligation

/-! Exploratory conversion from addition-step to successor-step hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceInductionConversion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open IPRAEqualityOnlyReference IPRAReferenceEqualityTools IPRAReferencePredecessor
open IPRAReferenceAddOneOpen IPRATheoryHilbertBridge
open IPRATheoryInstantiation IPRAOrderErasure IPRAErasedInductionObligation

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

def addStepBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  ∀⁰ (φ 🡒 IPRAErasedInductionShape.atStep φ)
def succStepBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  ∀⁰ (φ 🡒 atSucc φ)

def replaceAddWithSucc {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended referenceTheory ⊢!
      (Rew.embSubsts (Fin.cases (addOne x) args) ▹ φ) 🡒
      (Rew.embSubsts (Fin.cases (succ x) args) ▹ φ) :=
  (replaceParameter φ (addOne x) (succ x) args) ⨀ addOneOpen x

def stepConvert {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (args : Fin n → Term language ℕ) : extended referenceTheory ⊢!
      (Rew.embSubsts args ▹ addStepBody φ) 🡒
      (Rew.embSubsts args ▹ succStepBody φ) := by
  let u : Fin (n+1) → Term language ℕ := Fin.cases (&0) (fun i => Rew.shift (args i))
  have hcv : extended referenceTheory ⊢!
      Rew.free ▹ ((Rew.embSubsts args).q ▹ IPRAErasedInductionShape.atStep φ) 🡒
      Rew.free ▹ ((Rew.embSubsts args).q ▹ atSucc φ) := by
    have hA : (Rew.free : Rew language ℕ 1 ℕ 0).comp
        ((Rew.embSubsts args).q.comp (Rew.subst (Fin.cases (IPRAErasedInductionShape.stepTerm n) (fun i => #i.succ)))) =
        Rew.embSubsts (Fin.cases (addOne (&0)) (fun i => Rew.shift (args i))) := by
      ext i
      · cases i using Fin.cases with
        | zero =>
          simp [Rew.comp_app, Rew.func, IPRAErasedInductionShape.stepTerm, addOne, one, Function.comp_def]
          funext j; cases j using Fin.cases with
          | zero => rfl
          | succ j => cases j using Fin.cases with
            | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
            | succ j => exact Fin.elim0 j
        | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
      · exact Empty.elim i
    have hS : (Rew.free : Rew language ℕ 1 ℕ 0).comp
        ((Rew.embSubsts args).q.comp (Rew.subst (Fin.cases
          (applyCode .succ (fun _ => #0)) (fun i => #i.succ)))) =
        Rew.embSubsts (Fin.cases (succ (&0)) (fun i => Rew.shift (args i))) := by
      ext i
      · cases i using Fin.cases with
        | zero => simp [Rew.comp_app, Rew.func, applyCode, succ, Function.comp_def]
        | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
      · exact Empty.elim i
    simpa only [← TransitiveRewriting.comp_app, IPRAErasedInductionShape.atStep, atSucc, hA, hS] using
      replaceAddWithSucc φ (&0) (fun i => Rew.shift (args i))
  let p : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ φ
  let q : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ IPRAErasedInductionShape.atStep φ
  let r : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ atSucc φ
  have hpoint : extended referenceTheory ⊢! (Rewriting.free p 🡒 Rewriting.free q) 🡒
      (Rewriting.free p 🡒 Rewriting.free r) :=
    Entailment.implyS ⨀ Entailment.C_of_conseq hcv
  have hg : extended referenceTheory ⊢! ∀⁰ ((p 🡒 q) 🡒 (p 🡒 r)) := by
    apply HilbertProofᵢ.gen
    change extended referenceTheory ⊢! _
    simpa only [LogicalConnective.HomClass.map_imply] using hpoint
  have hforall := (HilbertProofᵢ.allImplyAllOfAllImply (p 🡒 q) (p 🡒 r)) ⨀ hg
  simpa only [addStepBody, succStepBody, Rewriting.app_all, LogicalConnective.HomClass.map_imply, p, q, r] using hforall

def additionInduction {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (hopen : IPRAQuantifierFree.OpenI φ) :
    referenceTheory ⊢! IPRAErasedInductionShape.inductionAxiom φ := by
  unfold IPRAErasedInductionShape.inductionAxiom
  apply IPRAReferenceCloseFamily.closeFamily referenceTheory n
  intro args
  have hind : referenceTheory ⊢! IPRAEqualityOnlyReference.inductionAxiom φ :=
    Axiomatized.prfAxm (ReferenceAxiom.induction φ hopen)
  have hi := instantiateTheory (T := referenceTheory)
    (atZero φ 🡒 succStepBody φ 🡒 ∀⁰ φ) hind args
  have hc := stepConvert φ args
  let b : Propositionᵢ language := Rew.embSubsts args ▹ atZero φ
  let a : Propositionᵢ language := Rew.embSubsts args ▹ addStepBody φ
  let s : Propositionᵢ language := Rew.embSubsts args ▹ succStepBody φ
  let r : Propositionᵢ language := Rew.embSubsts args ▹ (∀⁰ φ)
  have hi' : extended referenceTheory ⊢! b 🡒 (s 🡒 r) := by
    simpa only [LogicalConnective.HomClass.map_imply, b, s, r] using hi
  have hc' : extended referenceTheory ⊢! a 🡒 s := hc
  have hh : [a,b] ⊢[extended referenceTheory]! r := by
    have ha : [a,b] ⊢[extended referenceTheory]! a := Entailment.FiniteContext.byAxm₀
    have hb : [a,b] ⊢[extended referenceTheory]! b := Entailment.FiniteContext.byAxm₁
    exact (Entailment.FiniteContext.of hi') ⨀ hb ⨀ ((Entailment.FiniteContext.of hc') ⨀ ha)
  have h1 := Entailment.FiniteContext.deduct! ⟨hh⟩
  have h2 := Entailment.FiniteContext.deduct! h1
  have ht := Entailment.FiniteContext.toDef (Classical.choice h2)
  have hres : extended referenceTheory ⊢! b 🡒 (a 🡒 r) := by
    simpa using (ht ⨀ (Entailment.verum : extended referenceTheory ⊢! ⊤))
  simpa only [addStepBody, LogicalConnective.HomClass.map_imply, b, a, r] using hres

theorem erasedInductionImage {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1))
    (hopen : IPRAQuantifierFree.OpenI φ) :
    referenceTheory ⊢ erase (IPRANativeInduction.inductionAxiom φ) := by
  rw [IPRAErasedInductionShape.erase_inductionAxiom]
  exact ⟨additionInduction (erase φ) (erase_preserves_open φ hopen)⟩

theorem nativeToReference {σ : Sentenceᵢ PRALanguage.language}
    (h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ :=
  IPRAErasedInductionObligation.transfer (fun φ hopen => erasedInductionImage φ hopen) h

end DiophantineConsistency.IPRAReferenceInductionConversion
