import Foundation.FirstOrder.Intuitionistic.Deduction
import DiophantineConsistency.FoundationPAHFSyntax
import DiophantineConsistency.HADeduction

/-! # Foundation intuitionistic logic in actual HA natural deduction

The map constructs `HA.Derives` proofs and retains every finite assumption.
Only logical rules are translated. It does not assert that any translated
arithmetic axiom is an HA axiom or that a translated arithmetic theory proves
its intended sentence in HA.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFLogic
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax
open SetTheory.PA
open HA

private theorem axK (a b : Formula) : Derives [] (.imp a (.imp b a)) :=
  .impI _ _ _ (.impI _ _ _ (.ass _ _ (by simp)))

private theorem axS (a b c : Formula) :
    Derives [] (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have h₁ : Derives [a, .imp a b, .imp a (.imp b c)] (.imp a (.imp b c)) :=
    .ass _ _ (by simp)
  have h₂ : Derives [a, .imp a b, .imp a (.imp b c)] (.imp a b) := .ass _ _ (by simp)
  have ha : Derives [a, .imp a b, .imp a (.imp b c)] a := .ass _ _ (by simp)
  exact (h₁.mp ha).mp (h₂.mp ha)

private theorem axAnd (a b : Formula) : Derives [] (.imp a (.imp b (.and a b))) :=
  .impI _ _ _ (.impI _ _ _ (.andI _ _ _ (.ass _ _ (by simp)) (.ass _ _ (by simp))))

private theorem axOr (a b c : Formula) :
    Derives [] (.imp (.imp a c) (.imp (.imp b c) (.imp (.or a b) c))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.orE _ a b c (.ass _ _ (by simp))
  · exact (Derives.ass _ (.imp a c) (by simp)).mp (.ass _ a (by simp))
  · exact (Derives.ass _ (.imp b c) (by simp)).mp (.ass _ b (by simp))

/-- A shifted universal can be specialized at the fresh variable. -/
private theorem openShiftedAll {G : List Formula} {a : Formula}
    (h : Derives G (Formula.rename Nat.succ (.all a))) : Derives G a := by
  have hi := Derives.allE G (Formula.rename (SetTheory.up Nat.succ) a) (.var 0) h
  simpa only [Formula.subst_instTerm_var_zero_rename_up_succ] using hi

private theorem axAll (a b : Formula) :
    Derives [] (.imp (.all (.imp (Formula.rename Nat.succ a) b)) (.imp a (.all b))) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.allI
  have h : Derives ([a, .all (.imp (Formula.rename Nat.succ a) b)].map
      (Formula.rename Nat.succ))
      (Formula.rename Nat.succ (.all (.imp (Formula.rename Nat.succ a) b))) :=
    .ass _ _ (by simp)
  exact (openShiftedAll h).mp (.ass _ _ (by simp))

private theorem axEx (a b : Formula) :
    Derives [] (.imp (.all (.imp a (Formula.rename Nat.succ b))) (.imp (.ex a) b)) := by
  apply Derives.impI
  apply Derives.impI
  apply Derives.exE _ a b (.ass _ _ (by simp))
  have h : Derives (a :: ([.ex a, .all (.imp a (Formula.rename Nat.succ b))].map
      (Formula.rename Nat.succ)))
      (Formula.rename Nat.succ (.all (.imp a (Formula.rename Nat.succ b)))) :=
    .ass _ _ (by simp)
  exact (openShiftedAll h).mp (.ass _ _ List.mem_cons_self)

private theorem formulaInst (p : Semipropositionᵢ ℒₒᵣ 1) (t : SyntacticTerm ℒₒᵣ) :
    formula (p/[t]) = Formula.subst (Formula.instTerm (term t)) (formula p) := by
  have hv : (![t] : Fin 1 → SyntacticTerm ℒₒᵣ) = (fun _ => t) := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  change formula (p ⇜ ![t]) = _
  rw [hv]
  exact formula_inst p t

/-- A structural logical map. Its axiom-image hypothesis is explicit and is
fully discharged for the actual intuitionistic Hilbert system below. -/
theorem ofHilbertProof {Λ : Hilbertᵢ ℒₒᵣ}
    (hax : ∀ φ ∈ Λ, Derives [] (formula φ))
    {φ : Propositionᵢ ℒₒᵣ} (p : HilbertProofᵢ Λ φ) : Derives [] (formula φ) := by
  induction p with
  | eaxm h => exact hax _ h
  | mdp _ _ ih₁ ih₂ => exact ih₁.mp ih₂
  | gen p ih =>
      change Derives [] (formula (Semiformulaᵢ.all _))
      rw [formula_all]
      apply Derives.allI
      simpa only [List.map_nil, formula_free] using ih
  | verum => exact Derives.identity [] .bot
  | implyK p q => exact axK (formula p) (formula q)
  | implyS p q r => exact axS (formula p) (formula q) (formula r)
  | and₁ p q => exact Derives.and_left [] (formula p) (formula q)
  | and₂ p q => exact Derives.and_right [] (formula p) (formula q)
  | and₃ p q => exact axAnd (formula p) (formula q)
  | or₁ p q => exact .impI _ _ _ (.orI1 _ _ _ (.ass _ _ List.mem_cons_self))
  | or₂ p q => exact .impI _ _ _ (.orI2 _ _ _ (.ass _ _ List.mem_cons_self))
  | or₃ p q r => exact axOr (formula p) (formula q) (formula r)
  | all₁ p t =>
      change Derives [] (.imp (formula (.all p)) (formula (p/[t])))
      rw [formula_all, formulaInst]
      exact .impI _ _ _ (.allE _ _ _ (.ass _ _ List.mem_cons_self))
  | all₂ p q =>
      change Derives [] (.imp (formula (.all (.imp (p ⇜ Fin.elim0) q)))
        (.imp (formula p) (formula (.all q))))
      rw [formula_all, formula_all]
      change Derives [] (.imp (.all (.imp (formula (p ⇜ Fin.elim0)) (formula q)))
        (.imp (formula p) (.all (formula q))))
      rw [formula_empty_subst]
      exact axAll (formula p) (formula q)
  | ex₁ t p =>
      change Derives [] (.imp (formula (p/[t])) (formula (.exs p)))
      rw [formula_exs, formulaInst]
      exact .impI _ _ _ (.exI _ _ _ (.ass _ _ List.mem_cons_self))
  | ex₂ p q =>
      change Derives [] (.imp (formula (.all (.imp p (q ⇜ Fin.elim0))))
        (.imp (formula (.exs p)) (formula q)))
      rw [formula_all, formula_exs]
      change Derives [] (.imp (.all (.imp (formula p) (formula (q ⇜ Fin.elim0))))
        (.imp (.ex (formula p)) (formula q)))
      rw [formula_empty_subst]
      exact axEx (formula p) (formula q)

/-- No axiom-image oracle remains for Foundation's actual intuitionistic logic. -/
theorem intuitionistic_proof {φ : Propositionᵢ ℒₒᵣ}
    (p : HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ) φ) : Derives [] (formula φ) := by
  apply ofHilbertProof (p := p)
  intro ψ hψ
  obtain ⟨χ, rfl⟩ := hψ
  exact .impI _ _ _ (.botE _ _ (.ass _ _ List.mem_cons_self))

private theorem contextConjunction (Γ : List (Propositionᵢ ℒₒᵣ)) :
    Derives (Γ.map formula) (formula (⋀Γ)) := by
  induction Γ with
  | nil => exact Derives.identity [] .bot
  | cons p Γ ih =>
      cases Γ with
      | nil => exact .ass _ _ List.mem_cons_self
      | cons q Γ =>
          exact .andI _ _ _ (.ass _ _ List.mem_cons_self) (ih.prepend (formula p))

/-- The target uses the source's actual finite context, without discarding,
closing, or reclassifying its assumptions as arithmetic axioms. -/
theorem finite_proof {Γ : List (Propositionᵢ ℒₒᵣ)} {φ : Propositionᵢ ℒₒᵣ}
    (p : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)]! φ) : Derives (Γ.map formula) (formula φ) := by
  have h := intuitionistic_proof (LO.Entailment.FiniteContext.toDef p)
  have h' := h.weaken (Γ.map formula) (by simp)
  exact h'.mp (contextConjunction Γ)

/-- Proof existence is enough: no selection or serialization of a derivation
is required, and no classical-to-HA principle occurs. -/
theorem finite_provable {Γ : List (Propositionᵢ ℒₒᵣ)} {φ : Propositionᵢ ℒₒᵣ}
    (p : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)] φ) : Derives (Γ.map formula) (formula φ) := by
  obtain ⟨p⟩ := p
  exact finite_proof p

end DiophantineConsistency.FoundationPAHFLogic
