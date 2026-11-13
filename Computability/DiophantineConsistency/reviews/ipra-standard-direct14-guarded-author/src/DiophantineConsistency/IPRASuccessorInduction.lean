import DiophantineConsistency.IPRAOpenDisjunctionWitness
import DiophantineConsistency.IPRAAddOneDirect
import DiophantineConsistency.IPRAEqualitySymmetryGG
/-! Usual successor-step quantifier-free induction from the candidate native x+1 schema, for arbitrary finite parameters. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASuccessorInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
open DiophantineConsistency.IPRANativeDisjunctionWitness DiophantineConsistency.IPRADifferenceStepClosure DiophantineConsistency.IPRADifferenceSuccEq
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def replaceParameter {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (u v : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! eqAt u v 🡒
      ((Rew.embSubsts (Fin.cases u args) ▹ φ) 🡒 (Rew.embSubsts (Fin.cases v args) ▹ φ)) := by
  have ha : nativeTheory ⊢! eqSubstitutionI φ :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution φ))
  let vars : Fin (n+2) → Term language ℕ := Fin.cases u (Fin.cases v args)
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody φ) ha vars
  have hL : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #0 (fun i => #i.succ.succ))) =
      Rew.embSubsts (Fin.cases u args) := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app, vars]
      | succ j => simp [Rew.comp_app, vars]
    · exact Empty.elim i
  have varsOne : vars ((0 : Fin (n+1)).succ) = v := by
    dsimp only [vars]
    rw [Fin.cases_succ, Fin.cases_zero]
  have hR : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #1 (fun i => #i.succ.succ))) =
      Rew.embSubsts (Fin.cases v args) := by
    ext i
    · cases i using Fin.cases with
      | zero =>
        change vars ((0 : Fin (n+1)).succ) = v
        exact varsOne
      | succ j => simp [Rew.comp_app, vars]
    · exact Empty.elim i
  have he : (fun i : Fin 2 => Rew.embSubsts vars (![#0,#1] i)) = ![u,v] := by
    funext i; cases i using Fin.cases with
    | zero => simp [vars]
    | succ j => cases j using Fin.cases with
      | zero =>
        change vars ((0 : Fin (n+1)).succ) = v
        exact varsOne
      | succ j => exact Fin.elim0 j
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    ← TransitiveRewriting.comp_app, hL, hR, Semiformulaᵢ.rew_rel, he, eqAt] using hp
def succTerm (n : ℕ) : TermN (n+1) := .func Code.succ (fun _ => #0)
def atSucc {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+1) :=
  Rew.subst (Fin.cases (succTerm n) (fun i => #i.succ)) ▹ φ

def succStepBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  ∀⁰ (φ 🡒 atSucc φ)
def succInductionBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language n :=
  atZero φ 🡒 succStepBody φ 🡒 ∀⁰ φ
def succInductionAxiom {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Sentenceᵢ language :=
  ∀⁰* (succInductionBody φ)

def replaceSuccWithAdd {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended nativeTheory ⊢!
      (Rew.embSubsts (Fin.cases (sx x) args) ▹ φ) 🡒
      (Rew.embSubsts (Fin.cases (addOneTerm x) args) ▹ φ) := by
  have he := (symmetryOpen (addOneTerm x) (sx x)) ⨀ addOneOpen x
  exact (replaceParameter φ (sx x) (addOneTerm x) args) ⨀ he

def stepConvert {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (args : Fin n → Term language ℕ) : extended nativeTheory ⊢!
      (Rew.embSubsts args ▹ succStepBody φ) 🡒
      (Rew.embSubsts args ▹ (∀⁰ (φ 🡒 atStep φ))) := by
  let u : Fin (n+1) → Term language ℕ := Fin.cases (&0) (fun i => Rew.shift (args i))
  have hfree : (Rew.free : Rew language ℕ 1 ℕ 0).comp (Rew.embSubsts args).q = Rew.embSubsts u := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app, u]
      | succ j => simp [Rew.comp_app, Rew.free_bShift_app, u]
    · exact Empty.elim i
  have hsuc : (Rew.embSubsts u).comp (Rew.subst (Fin.cases (succTerm n) (fun i => #i.succ))) =
      Rew.embSubsts (Fin.cases (sx (&0)) (fun i => Rew.shift (args i))) := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app, Rew.func, succTerm, u, sx, Function.comp_def]
      | succ j => simp [Rew.comp_app, u]
    · exact Empty.elim i
  have hadd : (Rew.embSubsts u).comp (Rew.subst (Fin.cases (stepTerm n) (fun i => #i.succ))) =
      Rew.embSubsts (Fin.cases (addOneTerm (&0)) (fun i => Rew.shift (args i))) := by
    ext i
    · cases i using Fin.cases with
      | zero =>
        simp [Rew.comp_app, Rew.func, stepTerm, u, addOneTerm, Function.comp_def]
        funext j; cases j using Fin.cases with
        | zero => simp
        | succ j => cases j using Fin.cases with
          | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
          | succ j => exact Fin.elim0 j
      | succ j => simp [Rew.comp_app, u]
    · exact Empty.elim i
  have hcv : extended nativeTheory ⊢!
      Rew.free ▹ ((Rew.embSubsts args).q ▹ atSucc φ) 🡒
      Rew.free ▹ ((Rew.embSubsts args).q ▹ atStep φ) := by
    have hS : (Rew.free : Rew language ℕ 1 ℕ 0).comp
        ((Rew.embSubsts args).q.comp (Rew.subst (Fin.cases (succTerm n) (fun i => #i.succ)))) =
        Rew.embSubsts (Fin.cases (sx (&0)) (fun i => Rew.shift (args i))) := by
      ext i
      · cases i using Fin.cases with
        | zero => simp [Rew.comp_app, Rew.func, succTerm, sx, Function.comp_def]
        | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
      · exact Empty.elim i
    have hA : (Rew.free : Rew language ℕ 1 ℕ 0).comp
        ((Rew.embSubsts args).q.comp (Rew.subst (Fin.cases (stepTerm n) (fun i => #i.succ)))) =
        Rew.embSubsts (Fin.cases (addOneTerm (&0)) (fun i => Rew.shift (args i))) := by
      ext i
      · cases i using Fin.cases with
        | zero =>
          simp [Rew.comp_app, Rew.func, stepTerm, addOneTerm, Function.comp_def]
          funext j; cases j using Fin.cases with
          | zero => simp
          | succ j => cases j using Fin.cases with
            | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
            | succ j => exact Fin.elim0 j
        | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
      · exact Empty.elim i
    simpa only [← TransitiveRewriting.comp_app, atSucc, atStep, hS, hA] using
      replaceSuccWithAdd φ (&0) (fun i => Rew.shift (args i))
  let p : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ φ
  let q : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ atSucc φ
  let r : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ atStep φ
  have hpoint : extended nativeTheory ⊢! (Rewriting.free p 🡒 Rewriting.free q) 🡒
      (Rewriting.free p 🡒 Rewriting.free r) :=
    Entailment.implyS ⨀ Entailment.C_of_conseq hcv
  have hg : extended nativeTheory ⊢! ∀⁰ ((p 🡒 q) 🡒 (p 🡒 r)) := by
    apply HilbertProofᵢ.gen
    change extended nativeTheory ⊢! _
    simpa only [LogicalConnective.HomClass.map_imply] using hpoint
  have hforall := (HilbertProofᵢ.allImplyAllOfAllImply (p 🡒 q) (p 🡒 r)) ⨀ hg
  simpa only [succStepBody, Rewriting.app_all, LogicalConnective.HomClass.map_imply, p, q, r] using hforall
/-- The candidate's open x+1 induction schema proves the successor schema,
with all finite parameters retained. -/
def successorInduction {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (hopen : DiophantineConsistency.IPRAQuantifierFree.OpenI φ) :
    nativeTheory ⊢! succInductionAxiom φ := by
  apply closeFamily n (succInductionBody φ)
  intro args
  have hind : nativeTheory ⊢! inductionAxiom φ :=
    Axiomatized.prfAxm (NativeAxiom.induction ⟨n,φ,hopen,rfl⟩)
  have hi := instantiateTheory (T := nativeTheory) (inductionBody φ) hind args
  have hc := stepConvert φ args
  let b : Propositionᵢ language := Rew.embSubsts args ▹ atZero φ
  let s : Propositionᵢ language := Rew.embSubsts args ▹ succStepBody φ
  let p : Propositionᵢ language := Rew.embSubsts args ▹ (∀⁰ (φ 🡒 atStep φ))
  let r : Propositionᵢ language := Rew.embSubsts args ▹ (∀⁰ φ)
  have hi' : extended nativeTheory ⊢! b 🡒 (p 🡒 r) := by
    simpa only [inductionBody, LogicalConnective.HomClass.map_imply, b, p, r] using hi
  have hc' : extended nativeTheory ⊢! s 🡒 p := hc
  have hh : [s,b] ⊢[extended nativeTheory]! r := by
    have hs : [s,b] ⊢[extended nativeTheory]! s := Entailment.FiniteContext.byAxm₀
    have hb : [s,b] ⊢[extended nativeTheory]! b := Entailment.FiniteContext.byAxm₁
    exact (Entailment.FiniteContext.of hi') ⨀ hb ⨀ ((Entailment.FiniteContext.of hc') ⨀ hs)
  have h1 := Entailment.FiniteContext.deduct! ⟨hh⟩
  have h2 := Entailment.FiniteContext.deduct! h1
  have ht := Entailment.FiniteContext.toDef (Classical.choice h2)
  have hres : extended nativeTheory ⊢! b 🡒 (s 🡒 r) := by
    simpa using (ht ⨀ (Entailment.verum : extended nativeTheory ⊢! ⊤))
  simpa only [succInductionBody, LogicalConnective.HomClass.map_imply, b, s, r] using hres

end DiophantineConsistency.IPRASuccessorInduction
