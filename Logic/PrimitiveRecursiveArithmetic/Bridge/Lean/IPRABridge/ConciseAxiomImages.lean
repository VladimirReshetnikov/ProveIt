import IPRABridge.Syntax
import DiophantineConsistency.IPRAReferencePredecessor

/-! The Foundation reference theory proves the translated ConciseIPRA axioms. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open PRAFiniteFunctionCodes (Code pack)
open IPRAEqualityOnlyReference

local instance conciseAxiomLanguageDecidableEq : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

private theorem term_var {n : ℕ} (i : Fin n) :
    toFoundationTerm (Syn.var i) = #i := rfl

private theorem term_zero {n : ℕ} :
    toFoundationTerm (PTm.zero : PTm n) = applyCode (.zero 0) Fin.elim0 := by
  unfold PTm.zero
  rw [toFoundationTerm, toFoundationCode, applyCode]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem term_succ {n : ℕ} (t : PTm n) :
    toFoundationTerm (PTm.succ t) = applyCode .succ (fun _ => toFoundationTerm t) := rfl

private theorem term_cases {n k : ℕ} (t : PTm n) (v : Fin k → PTm n) :
    (fun i => toFoundationTerm (Fin.cases t v i)) =
      Fin.cases (toFoundationTerm t) (fun i => toFoundationTerm (v i)) := by
  exact funext (Fin.cases rfl (fun _ => rfl))

private theorem term_inst {n : ℕ} (t : PTm n) :
    (fun i => toFoundationTerm (Syn.inst t i)) =
      Fin.cases (toFoundationTerm t) (fun i => #i) := term_cases t Syn.var

private theorem term_repl {n : ℕ} (t : PTm (n + 1)) :
    (fun i => toFoundationTerm (Syn.repl t i)) =
      Fin.cases (toFoundationTerm t) (fun i => #i.succ) :=
  term_cases t (fun i => Syn.var i.succ)

private theorem vars_succ (n : ℕ) :
    (fun i : Fin (n + 1) => (#i : TermN (n + 1))) = Fin.cases #0 (fun i => #i.succ) :=
  funext (Fin.cases rfl (fun _ => rfl))

/-- Each open arithmetic axiom translates to a theorem after universal closure. -/
theorem concise_axiom_image {n : ℕ} {φ : Fm PTm n} (h : PRAAx n φ) :
    referenceTheory ⊢ ∀⁰* (toFoundation φ) := by
  cases h with
  | proj i => exact ⟨Axiomatized.prfAxm (ReferenceAxiom.defining (.projection i))⟩
  | comp f gs =>
    have hd : referenceTheory ⊢ compositionEquation (toFoundationCode f)
        (pack _ (fun i => toFoundationCode (gs i))) :=
      ⟨Axiomatized.prfAxm (ReferenceAxiom.defining (.composition _ _))⟩
    simpa only [compositionEquation, equalClosure, applyCode, vars, getCode_pack,
      toFoundation, toFoundationTerm, toFoundationCode, term_var] using! hd
  | precZero f g =>
    have hd : referenceTheory ⊢ recursionBaseEquation (toFoundationCode f) (toFoundationCode g) :=
      ⟨Axiomatized.prfAxm (ReferenceAxiom.defining (.recursionBase _ _))⟩
    simpa only [recursionBaseEquation, equalClosure, vars, toFoundation, toFoundationTerm,
      toFoundationCode, term_inst, term_var, term_zero, applyCode] using! hd
  | @precSucc k f g =>
    have hd : referenceTheory ⊢ recursionStepEquation (toFoundationCode f) (toFoundationCode g) :=
      ⟨Axiomatized.prfAxm (ReferenceAxiom.defining (.recursionStep _ _))⟩
    simp only [recursionStepEquation, equalClosure, applyCode] at hd
    simp only [toFoundation, toFoundationTerm, toFoundationCode,
      term_repl, term_cases, term_succ, term_var, applyCode]
    rw [vars_succ k]
    exact hd
  | succNeZero =>
    have hd : referenceTheory ⊢ successorNonzero :=
      ⟨Axiomatized.prfAxm ReferenceAxiom.successorNonzero⟩
    simpa only [successorNonzero, toFoundation, term_succ, term_var, term_zero] using! hd
  | succInj =>
    have hd := IPRAReferencePredecessor.successorInjectivityImage
    rw [IPRAErasedSuccessorShape.erase_successorInjectivity] at hd
    exact ⟨hd⟩
  | ind φ hφ =>
    have hd : referenceTheory ⊢ inductionAxiom (toFoundation φ) :=
      ⟨Axiomatized.prfAxm (ReferenceAxiom.induction _ ((toFoundation_open φ).2 hφ))⟩
    simpa only [inductionAxiom, atZero, atSucc, toFoundation, toFoundation_subst,
      term_inst, term_repl, term_zero, term_succ, term_var] using! hd

end IPRABridge
