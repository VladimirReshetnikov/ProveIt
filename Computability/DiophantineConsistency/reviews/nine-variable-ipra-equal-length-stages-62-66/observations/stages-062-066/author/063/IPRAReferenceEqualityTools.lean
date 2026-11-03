import DiophantineConsistency.IPRAReferenceCloseFamily

/-! Exploratory open-instance tools for reference-theory Leibniz equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceEqualityTools
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

def eqAt (a b : Term language ℕ) : Propositionᵢ language := .rel EqualityRel.eq ![a,b]

def leibnizBody {n : ℕ} (φ : Semisentenceᵢ language (n+1)) : Semisentenceᵢ language (n+2) :=
  (.rel EqualityRel.eq ![#0,#1]) 🡒 (eqLeft φ 🡒 eqRight φ)

def replaceParameter {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (u v : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended referenceTheory ⊢! eqAt u v 🡒
      ((Rew.embSubsts (Fin.cases u args) ▹ φ) 🡒 (Rew.embSubsts (Fin.cases v args) ▹ φ)) := by
  have ha : referenceTheory ⊢! eqSubstitution φ :=
    Axiomatized.prfAxm (ReferenceAxiom.equality (EqualityAxiom.substitution φ))
  let vars : Fin (n+2) → Term language ℕ := Fin.cases u (Fin.cases v args)
  have hp := instantiateTheory (T := referenceTheory) (leibnizBody φ) ha vars
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
      | zero => change vars ((0 : Fin (n+1)).succ) = v; exact varsOne
      | succ j => simp [Rew.comp_app, vars]
    · exact Empty.elim i
  have he : (fun i : Fin 2 => Rew.embSubsts vars (![#0,#1] i)) = ![u,v] := by
    funext i; cases i using Fin.cases with
    | zero => simp [vars]
    | succ j => cases j using Fin.cases with
      | zero => change vars ((0 : Fin (n+1)).succ) = v; exact varsOne
      | succ j => exact Fin.elim0 j
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    ← TransitiveRewriting.comp_app, hL, hR, Semiformulaᵢ.rew_rel, he, eqAt] using hp

end DiophantineConsistency.IPRAReferenceEqualityTools
