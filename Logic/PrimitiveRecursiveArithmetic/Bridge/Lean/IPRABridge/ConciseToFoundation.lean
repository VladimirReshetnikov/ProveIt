import IPRABridge.Syntax
import IPRABridge.ConciseToFoundationLogic
import ConciseIPRA.Deduction
import DiophantineConsistency.IPRAReferenceCloseFamily

/-! Interpret ConciseIPRA natural deduction in the Foundation reference calculus. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open Rewriting
open LeanProofs.ConciseIPRA (Fm PTm Prf Syn)
open DiophantineConsistency.PRAFiniteFunctionCodes (Code)
open DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.IPRAReferenceEqualityTools (eqAt)
open DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation
open ConciseToFoundationLogic

local instance conciseToFoundationLanguageDecidableEq : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

local notation "Λ" => extended referenceTheory

/-- Translate a ConciseIPRA formula under an assignment of Foundation terms. -/
abbrev toFoundationInEnv {n : ℕ} (v : Fin n → Term language ℕ) (p : Fm PTm n) : Propositionᵢ language :=
  atEnv v (toFoundation p)

private theorem inEnv_subst {m n : ℕ} (v : Fin n → Term language ℕ) (s : Fin m → PTm n) (p : Fm PTm m) :
    toFoundationInEnv v (p.subst s) = atEnv (fun i => Rew.embSubsts v (toFoundationTerm (s i))) (toFoundation p) := by
  change atEnv v (toFoundation (p.subst s)) = _
  rw [toFoundation_subst, atEnv_subst]

private theorem inEnv_inst {n : ℕ} (v : Fin n → Term language ℕ) (t : PTm n) (p : Fm PTm (n + 1)) :
    toFoundationInEnv v (p.subst (Syn.inst t)) =
      ((Rew.embSubsts v).q ▹ toFoundation p)/[Rew.embSubsts v (toFoundationTerm t)] := by
  rw [inEnv_subst, atEnv_specialize]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

private theorem inEnv_shift {n : ℕ} (v : Fin n → Term language ℕ) (p : Fm PTm n) :
    toFoundationInEnv (liftEnv v) p.shift = shift (toFoundationInEnv v p) := by
  change atEnv (liftEnv v) (toFoundation (p.subst (fun i => Syn.var i.succ))) = _
  rw [toFoundation_subst]
  exact atEnv_lift_shift v (toFoundation p)

private theorem map_inEnv_shift {n : ℕ} (v : Fin n → Term language ℕ) (Γ : List (Fm PTm n)) :
    (Γ.map Fm.shift).map (toFoundationInEnv (liftEnv v)) = (Γ.map (toFoundationInEnv v))⁺ := by
  simp [shifts, List.map_map, Function.comp_def, inEnv_shift]

private theorem inEnv_eq {n : ℕ} (v : Fin n → Term language ℕ) (t u : PTm n) :
    toFoundationInEnv v (.eq t u) = eqAt (Rew.embSubsts v (toFoundationTerm t))
      (Rew.embSubsts v (toFoundationTerm u)) := by
  unfold toFoundationInEnv atEnv eqAt
  rw [toFoundation, Semiformulaᵢ.rew_rel]
  congr 1
  exact funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))

private theorem inEnv_lift {n : ℕ} (v : Fin n → Term language ℕ) (p : Fm PTm (n + 1)) :
    free ((Rew.embSubsts v).q ▹ toFoundation p) = toFoundationInEnv (liftEnv v) p :=
  atEnv_lift v (toFoundation p)

/-- Every ConciseIPRA derivation transports to a Foundation finite-context
derivation, provided Foundation proves the universal closures of the axiom images. -/
theorem toFoundation_provable_of_axioms {Ax : LeanProofs.ConciseIPRA.Theory PTm}
    (hAx : ∀ {k : ℕ} {p : Fm PTm k}, Ax k p → referenceTheory ⊢ ∀⁰* (toFoundation p))
    {n : ℕ} {Γ : List (Fm PTm n)} {p : Fm PTm n} (d : Prf Ax Γ p) (v : Fin n → Term language ℕ) :
    (Γ.map (toFoundationInEnv v)) ⊢[Λ] toFoundationInEnv v p := by
  induction d with
  | hyp h => exact ⟨FiniteContext.byAxm (List.mem_map_of_mem h)⟩
  | ax h s =>
    rw [inEnv_subst]
    exact ⟨of (instantiateTheory _ (hAx h).some _)⟩
  | botE p _ ih =>
    have hefq : Λ ⊢! ⊥ 🡒 toFoundationInEnv v p :=
      HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic, Axioms.EFQ]))
    exact ⟨of hefq ⨀ (ih v).some⟩
  | andI _ _ ih₁ ih₂ => exact ⟨Entailment.K_intro (ih₁ v).some (ih₂ v).some⟩
  | andE₁ _ ih => exact ⟨Entailment.K_left (ih v).some⟩
  | andE₂ _ ih => exact ⟨Entailment.K_right (ih v).some⟩
  | orI₁ _ ih => exact ⟨Entailment.or₁ ⨀ (ih v).some⟩
  | orI₂ _ ih => exact ⟨Entailment.or₂ ⨀ (ih v).some⟩
  | orE _ _ _ ih ih₁ ih₂ =>
    exact ⟨Entailment.or₃ ⨀ deduct (ih₁ v).some ⨀ deduct (ih₂ v).some ⨀ (ih v).some⟩
  | impI _ ih => exact ⟨deduct (ih v).some⟩
  | impE _ _ ih₁ ih₂ => exact ⟨(ih₁ v).some ⨀ (ih₂ v).some⟩
  | @allI n Γ p _ ih =>
    have hBody := (ih (liftEnv v)).some
    rw [map_inEnv_shift, ← inEnv_lift v p] at hBody
    exact ⟨HilbertProofᵢ.geNOverFiniteContext hBody⟩
  | allE t _ ih =>
    rw [inEnv_inst]
    exact ⟨HilbertProofᵢ.specializeOverContext (ih v).some _⟩
  | @exI n Γ p t _ ih =>
    have hBody := (ih v).some
    rw [inEnv_inst] at hBody
    exact ⟨of (HilbertProofᵢ.ex₁ _ _) ⨀ hBody⟩
  | @exE n Γ p q _ _ ih₁ ih₂ =>
    have hBody := (ih₂ (liftEnv v)).some
    rw [List.map_cons, map_inEnv_shift, inEnv_shift, ← inEnv_lift v p] at hBody
    exact ⟨exElim (ih₁ v).some hBody⟩
  | eqRefl t =>
    rw [inEnv_eq]
    exact ⟨of (eqReflAt _)⟩
  | eqSubst p s t _ _ ih₁ ih₂ =>
    rw [inEnv_subst]
    apply replaceEnv (toFoundation p) (fun i => Rew.embSubsts v (toFoundationTerm (s i)))
    · intro i
      simpa only [inEnv_eq] using ih₁ i v
    · simpa only [inEnv_subst] using ih₂ v

/-- In an empty context, the translated formula can be universally closed. -/
theorem toFoundation_universal_of_axioms {Ax : LeanProofs.ConciseIPRA.Theory PTm}
    (hAx : ∀ {k : ℕ} {p : Fm PTm k}, Ax k p → referenceTheory ⊢ ∀⁰* (toFoundation p))
    {n : ℕ} {p : Fm PTm n} (d : Prf Ax [] p) : referenceTheory ⊢ ∀⁰* (toFoundation p) :=
  ⟨DiophantineConsistency.IPRAReferenceCloseFamily.closeFamily referenceTheory n (toFoundation p)
    (fun v => emptyPrf (toFoundation_provable_of_axioms hAx d v).some)⟩

/-- In particular, closed ConciseIPRA theorems translate to Foundation theorems. -/
theorem toFoundation_closed_of_axioms {Ax : LeanProofs.ConciseIPRA.Theory PTm}
    (hAx : ∀ {k : ℕ} {p : Fm PTm k}, Ax k p → referenceTheory ⊢ ∀⁰* (toFoundation p))
    {p : Fm PTm 0} (d : Prf Ax [] p) : referenceTheory ⊢ toFoundation p :=
  toFoundation_universal_of_axioms hAx d

end IPRABridge
