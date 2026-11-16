import DiophantineConsistency.IPRAReferenceEqualityTools

/-! Finite-context quantifier and equality rules for the Foundation reference theory. -/

set_option autoImplicit false

namespace IPRABridge.ConciseToFoundationLogic

open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open Rewriting

section Rewriting

variable {language : Language}

/-- Interpret each bound index of an open formula as a term with named variables. -/
def atEnv {n : ℕ} (v : Fin n → Term language ℕ) (p : Semisentenceᵢ language n) :
    Propositionᵢ language := Rew.embSubsts v ▹ p

/-- Extend the environment with a fresh variable for generalization. -/
def liftEnv {n : ℕ} (v : Fin n → Term language ℕ) : Fin (n + 1) → Term language ℕ :=
  Fin.cases &0 (fun j => Rew.shift (v j))

theorem atEnv_subst {m n : ℕ} (v : Fin n → Term language ℕ) (s : Fin m → Semiterm language Empty n)
    (p : Semisentenceᵢ language m) :
    atEnv v (Rew.subst s ▹ p) = atEnv (fun i => Rew.embSubsts v (s i)) p := by
  unfold atEnv
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext i
  · simp [Rew.comp_app]
  · exact Empty.elim i

theorem atEnv_lift {n : ℕ} (v : Fin n → Term language ℕ)
    (p : Semisentenceᵢ language (n + 1)) :
    free ((Rew.embSubsts v).q ▹ p) = atEnv (liftEnv v) p := by
  unfold atEnv
  show Rew.free ▹ ((Rew.embSubsts v).q ▹ p) = _
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext i
  · cases i using Fin.cases with
    | zero => simp [Rew.comp_app, liftEnv]
    | succ j => simp [Rew.comp_app, Rew.free_bShift_app, liftEnv]
  · exact Empty.elim i

theorem atEnv_lift_shift {n : ℕ} (v : Fin n → Term language ℕ)
    (p : Semisentenceᵢ language n) :
    atEnv (liftEnv v) (Rew.subst (fun i => #i.succ) ▹ p) = shift (atEnv v p) := by
  unfold atEnv
  show Rew.embSubsts (liftEnv v) ▹ (Rew.subst (fun i => #i.succ) ▹ p) =
    Rew.shift ▹ (Rew.embSubsts v ▹ p)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext i
  · simp [Rew.comp_app, liftEnv]
  · exact Empty.elim i

theorem atEnv_specialize {n : ℕ} (v : Fin n → Term language ℕ) (t : Term language ℕ)
    (p : Semisentenceᵢ language (n + 1)) :
    ((Rew.embSubsts v).q ▹ p)/[t] = atEnv (Fin.cases t v) p := by
  unfold atEnv
  show Rew.subst ![t] ▹ ((Rew.embSubsts v).q ▹ p) = _
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext i
  · cases i using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ j => simp [Rew.comp_app]
  · exact Empty.elim i

def exElim {Λ : Hilbertᵢ language} {Γ : List (Propositionᵢ language)} {A : Semipropositionᵢ language 1}
    {B : Propositionᵢ language} (hEx : Γ ⊢[Λ]! ∃⁰ A)
    (hBody : (free A :: Γ⁺) ⊢[Λ]! shift B) : Γ ⊢[Λ]! B := by
  have h : Γ⁺ ⊢[Λ]! free (A 🡒 B/[]) := by
    simpa using (deduct hBody)
  exact of (HilbertProofᵢ.ex₂ A B) ⨀ HilbertProofᵢ.geNOverFiniteContext h ⨀ hEx

end Rewriting

open DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.PRAFiniteFunctionCodes (Code)
open DiophantineConsistency.IPRAReferenceEqualityTools
open DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

local notation "Λ" => extended referenceTheory

noncomputable def eqReflAt (t : Term language ℕ) : Λ ⊢! eqAt t t := by
  let p : Semisentenceᵢ language 1 := .rel EqualityRel.eq ![#0, #0]
  have h : referenceTheory ⊢! ∀⁰* p :=
    Axiomatized.prfAxm (ReferenceAxiom.equality EqualityAxiom.refl)
  have hp := instantiateTheory p h (fun _ => t)
  have hArgs : (fun i : Fin 2 => Rew.embSubsts (fun _ : Fin 1 => t) (![#0, #0] i)) = ![t, t] := by
    refine funext (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) <;> simp
  simpa only [p, eqAt, Semiformulaᵢ.rew_rel, hArgs] using hp

private noncomputable def replaceAt {n : ℕ} (p : Semisentenceᵢ language n) (i : Fin n)
    (v : Fin n → Term language ℕ) (t u : Term language ℕ) :
    Λ ⊢! eqAt t u 🡒 atEnv (Function.update v i t) p 🡒 atEnv (Function.update v i u) p := by
  let select : Fin n → TermN (n + 1) := fun j => if j = i then #0 else #j.succ
  have aux (w : Term language ℕ) :
      atEnv (Fin.cases w v) (Rew.subst select ▹ p) = atEnv (Function.update v i w) p := by
    rw [atEnv_subst]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [select, hj]
  have h := replaceParameter (Rew.subst select ▹ p) t u v
  change Λ ⊢! eqAt t u 🡒 atEnv (Fin.cases t v) (Rew.subst select ▹ p) 🡒
    atEnv (Fin.cases u v) (Rew.subst select ▹ p) at h
  simpa only [aux] using h

/-- Simultaneous equality replacement follows by changing one parameter at a time. -/
theorem replaceEnv {n : ℕ} {Γ : List (Propositionᵢ language)} (p : Semisentenceᵢ language n)
    (v w : Fin n → Term language ℕ) (hEq : ∀ i, Γ ⊢[Λ] eqAt (v i) (w i))
    (hBody : Γ ⊢[Λ] atEnv v p) : Γ ⊢[Λ] atEnv w p := by
  let mix (s : Finset (Fin n)) : Fin n → Term language ℕ := fun i => if i ∈ s then w i else v i
  have hMix (s : Finset (Fin n)) : Γ ⊢[Λ] atEnv (mix s) p := by
    induction s using Finset.induction_on with
    | empty => simpa [mix] using hBody
    | @insert i s hi ih =>
      have hNext : mix (insert i s) = Function.update (mix s) i (w i) := by
        funext j
        by_cases hj : j = i <;> simp [mix, hj]
      have hEq' : Γ ⊢[Λ] eqAt (mix s i) (w i) := by
        simpa [mix, hi] using hEq i
      have hSub := of (Γ := Γ) (replaceAt p i (mix s) (mix s i) (w i))
      rw [Function.update_eq_self, ← hNext] at hSub
      exact ⟨hSub ⨀ hEq'.some ⨀ ih.some⟩
  simpa [mix] using hMix Finset.univ

end IPRABridge.ConciseToFoundationLogic
