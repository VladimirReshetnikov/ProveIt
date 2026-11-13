import DiophantineConsistency.IPRAAddOneGeneral
import DiophantineConsistency.IPRASuccessorInduction
/-! Successor-to-x+1 induction conversion in arbitrary theories with defining and equality schemas. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASuccessorInductionConverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
open DiophantineConsistency.IPRASuccessorInduction DiophantineConsistency.IPRAAddOneGeneral
open DiophantineConsistency.IPRADifferenceStepClosure DiophantineConsistency.IPRADifferenceSuccEq
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
def replaceParameterT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢! σ) {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (u v : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended T ⊢! eqAt u v 🡒
      ((Rew.embSubsts (Fin.cases u args) ▹ φ) 🡒 (Rew.embSubsts (Fin.cases v args) ▹ φ)) := by
  have ha : T ⊢! eqSubstitutionI φ := heq _ (EqualityAxiomI.substitution φ)
  let vars : Fin (n+2) → Term language ℕ := Fin.cases u (Fin.cases v args)
  have hp := instantiateTheory (T := T) (leibnizBody φ) ha vars
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
def addOneOpenT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (hadd : T ⊢ DiophantineConsistency.IPRAAddOneDirect.addOneI) (x : Term language ℕ) : extended T ⊢! eqAt (addOneTerm x) (sx x) := by
  let m : Semisentenceᵢ language 1 := .rel .eq ![stepTerm 0, .func Code.succ (fun _ => #0)]
  have hp := instantiateTheory (T := T) m (Classical.choice hadd) ![x]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![x] (![stepTerm 0, .func Code.succ (fun _ => #0)] i)) =
      ![addOneTerm x,sx x] := by
    funext i; cases i using Fin.cases with
    | zero =>
      simp [stepTerm, addOneTerm, Rew.func, Function.comp_def]
      funext j; cases j using Fin.cases with
      | zero => simp
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def, sx]
      | succ j => exact Fin.elim0 j
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def replaceAddWithSuccT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢! σ)
    (hadd : T ⊢ DiophantineConsistency.IPRAAddOneDirect.addOneI)
    {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended T ⊢! (Rew.embSubsts (Fin.cases (addOneTerm x) args) ▹ φ) 🡒
      (Rew.embSubsts (Fin.cases (sx x) args) ▹ φ) := by
  exact (replaceParameterT heq φ (addOneTerm x) (sx x) args) ⨀ addOneOpenT hadd x

def stepConvertT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢! σ)
    (haddProof : T ⊢ DiophantineConsistency.IPRAAddOneDirect.addOneI) {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (args : Fin n → Term language ℕ) : extended T ⊢!
      (Rew.embSubsts args ▹ (∀⁰ (φ 🡒 atStep φ))) 🡒
      (Rew.embSubsts args ▹ succStepBody φ) := by
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
  have hcv : extended T ⊢!
      Rew.free ▹ ((Rew.embSubsts args).q ▹ atStep φ) 🡒
      Rew.free ▹ ((Rew.embSubsts args).q ▹ atSucc φ) := by
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
      replaceAddWithSuccT heq haddProof φ (&0) (fun i => Rew.shift (args i))
  let p : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ φ
  let q : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ atStep φ
  let r : Semipropositionᵢ language 1 := (Rew.embSubsts args).q ▹ atSucc φ
  have hpoint : extended T ⊢! (Rewriting.free p 🡒 Rewriting.free q) 🡒
      (Rewriting.free p 🡒 Rewriting.free r) :=
    Entailment.implyS ⨀ Entailment.C_of_conseq hcv
  have hg : extended T ⊢! ∀⁰ ((p 🡒 q) 🡒 (p 🡒 r)) := by
    apply HilbertProofᵢ.gen
    change extended T ⊢! _
    simpa only [LogicalConnective.HomClass.map_imply] using hpoint
  have hforall := (HilbertProofᵢ.allImplyAllOfAllImply (p 🡒 q) (p 🡒 r)) ⨀ hg
  simpa only [succStepBody, Rewriting.app_all, LogicalConnective.HomClass.map_imply, p, q, r] using hforall
def closeFamilyT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)} : ∀ (n : ℕ) (φ : Semisentenceᵢ language n),
    (∀ v : Fin n → Term language ℕ, extended T ⊢! Rew.embSubsts v ▹ φ) →
    T ⊢! ∀⁰* φ
  | 0, φ, h => by
    have hp := h Fin.elim0
    have hr : (Rew.embSubsts (Fin.elim0 : Fin 0 → Term language ℕ)) = (Rew.emb : Rew language Empty 0 ℕ 0) := by
      ext i
      · exact Fin.elim0 i
      · exact Empty.elim i
    rw [hr] at hp
    apply extendedToTheory T
    simpa only [allClosure_zero, Rewriting.emb] using hp
  | n+1, φ, h => by
    have hh (v : Fin n → Term language ℕ) : extended T ⊢! Rew.embSubsts v ▹ (∀⁰ φ) := by
      apply HilbertProofᵢ.gen
      have hp := h (Fin.cases (&0) (fun i => Rew.shift (v i)))
      have hr : (Rew.free : Rew language ℕ 1 ℕ 0).comp (Rew.embSubsts v).q =
          Rew.embSubsts (Fin.cases (&0) (fun i => Rew.shift (v i))) := by
        ext i
        · cases i using Fin.cases with
          | zero => simp [Rew.comp_app]
          | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
        · exact Empty.elim i
      change extended T ⊢! Rew.free ▹ ((Rew.embSubsts v).q ▹ φ)
      rw [← TransitiveRewriting.comp_app, hr]
      exact hp
    have hc := closeFamilyT n (∀⁰ φ) hh
    simpa only [allClosure_succ] using hc
/-- In any intuitionistic theory proving the defining and equality axioms,
the successor induction instance entails the corresponding x+1 instance. -/
def plusInductionFromSucc {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (hdef : ∀ σ, DefiningEquationI σ → T ⊢! σ)
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢! σ)
    {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (hsucc : T ⊢! succInductionAxiom φ) : T ⊢! inductionAxiom φ := by
  have hadd : T ⊢ DiophantineConsistency.IPRAAddOneDirect.addOneI :=
    addOne (fun σ h => ⟨hdef σ h⟩) (fun σ h => ⟨heq σ h⟩)
  apply closeFamilyT n (inductionBody φ)
  intro args
  have hi := instantiateTheory (T := T) (succInductionBody φ) hsucc args
  have hc := stepConvertT heq hadd φ args
  let b : Propositionᵢ language := Rew.embSubsts args ▹ atZero φ
  let s : Propositionᵢ language := Rew.embSubsts args ▹ succStepBody φ
  let p : Propositionᵢ language := Rew.embSubsts args ▹ (∀⁰ (φ 🡒 atStep φ))
  let r : Propositionᵢ language := Rew.embSubsts args ▹ (∀⁰ φ)
  have hi' : extended T ⊢! b 🡒 (s 🡒 r) := by
    simpa only [succInductionBody, LogicalConnective.HomClass.map_imply, b, s, r] using hi
  have hc' : extended T ⊢! p 🡒 s := hc
  have hh : [p,b] ⊢[extended T]! r := by
    have hp : [p,b] ⊢[extended T]! p := Entailment.FiniteContext.byAxm₀
    have hb : [p,b] ⊢[extended T]! b := Entailment.FiniteContext.byAxm₁
    exact (Entailment.FiniteContext.of hi') ⨀ hb ⨀ ((Entailment.FiniteContext.of hc') ⨀ hp)
  have h1 := Entailment.FiniteContext.deduct! ⟨hh⟩
  have h2 := Entailment.FiniteContext.deduct! h1
  have ht := Entailment.FiniteContext.toDef (Classical.choice h2)
  have hres : extended T ⊢! b 🡒 (p 🡒 r) := by
    simpa using (ht ⨀ (Entailment.verum : extended T ⊢! ⊤))
  simpa only [inductionBody, LogicalConnective.HomClass.map_imply, b, p, r] using hres
end DiophantineConsistency.IPRASuccessorInductionConverse
