import ConciseIPRA.Deduction

/-! First-order soundness for the scoped deduction calculus. A term model
supplies its evaluation and substitution law. The theory's axioms are a
separate hypothesis of soundness. -/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

/-- A substitution-compatible evaluation of terms in a domain `V`. -/
structure TermModel (T : ℕ → Type) [Syn T] (V : Type*) where
  eval : ∀ {n}, T n → (Fin n → V) → V
  eval_var : ∀ {n} (i : Fin n) (e : Fin n → V), eval (var i) e = e i
  eval_subst : ∀ {n m} (σ : Fin n → T m) (t : T n) (e : Fin m → V),
    eval (Syn.subst σ t) e = eval t (fun i => eval (σ i) e)

namespace TermModel

variable {T : ℕ → Type} [Syn T] {V : Type*} (M : TermModel T V)

/-- Truth of an open formula at an assignment. -/
def Holds : {n : ℕ} → Fm T n → (Fin n → V) → Prop
  | _, .eq s t, e => M.eval s e = M.eval t e
  | _, .bot, _ => False
  | _, .and a b, e => Holds a e ∧ Holds b e
  | _, .or a b, e => Holds a e ∨ Holds b e
  | _, .imp a b, e => Holds a e → Holds b e
  | _, .all a, e => ∀ x, Holds a (Fin.cases x e)
  | _, .ex a, e => ∃ x, Holds a (Fin.cases x e)

private theorem eval_up {n m : ℕ} (σ : Fin n → T m) (e : Fin m → V) (x : V) :
    (fun i => M.eval (up σ i) (Fin.cases x e)) = Fin.cases x (fun i => M.eval (σ i) e) := by
  refine funext (Fin.cases ?_ (fun i => ?_))
  · simp [M.eval_var]
  · simp [Syn.shift, M.eval_var, M.eval_subst]

theorem holds_subst {n m : ℕ} (a : Fm T n) (σ : Fin n → T m) (e : Fin m → V) :
    M.Holds (a.subst σ) e ↔ M.Holds a (fun i => M.eval (σ i) e) := by
  induction a generalizing m with
  | eq s t => simp [Holds, M.eval_subst]
  | bot => rfl
  | and a b ihA ihB => simp [Holds, ihA, ihB]
  | or a b ihA ihB => simp [Holds, ihA, ihB]
  | imp a b ihA ihB => simp [Holds, ihA, ihB]
  | all a ih => simp [Holds, ih, M.eval_up]
  | ex a ih => simp [Holds, ih, M.eval_up]

private theorem holds_shift {n : ℕ} (a : Fm T n) (e : Fin n → V) (x : V) :
    M.Holds a.shift (Fin.cases x e) ↔ M.Holds a e := by
  simp [Fm.shift, M.holds_subst, M.eval_var]

private theorem holds_inst {n : ℕ} (a : Fm T (n + 1)) (t : T n) (e : Fin n → V) :
    M.Holds (a.subst (inst t)) e ↔ M.Holds a (Fin.cases (M.eval t e) e) := by
  rw [M.holds_subst]
  have he : (fun i => M.eval (inst t i) e) = Fin.cases (M.eval t e) e := by
    refine funext (Fin.cases ?_ (fun i => ?_))
    · rfl
    · simp [M.eval_var]
  rw [he]

/-- Soundness at every assignment satisfying the hypotheses. -/
theorem sound {Ax : Theory T}
    (valid : ∀ {n} {a : Fm T n}, Ax n a → ∀ e, M.Holds a e)
    {n : ℕ} {Γ : List (Fm T n)} {a : Fm T n} (h : Γ ⊢[Ax] a) (e : Fin n → V)
    (hΓ : ∀ b ∈ Γ, M.Holds b e) : M.Holds a e := by
  induction h with
  | hyp ha => exact hΓ _ ha
  | ax ha σ => exact (M.holds_subst _ σ e).2 (valid ha _)
  | botE _ _ ih => exact (ih e hΓ).elim
  | andI _ _ ih₁ ih₂ => exact ⟨ih₁ e hΓ, ih₂ e hΓ⟩
  | andE₁ _ ih => exact (ih e hΓ).1
  | andE₂ _ ih => exact (ih e hΓ).2
  | orI₁ _ ih => exact Or.inl (ih e hΓ)
  | orI₂ _ ih => exact Or.inr (ih e hΓ)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact (ih e hΓ).elim (fun h => ih₁ e (List.forall_mem_cons.2 ⟨h, hΓ⟩))
      (fun h => ih₂ e (List.forall_mem_cons.2 ⟨h, hΓ⟩))
  | impI _ ih => exact fun h => ih e (List.forall_mem_cons.2 ⟨h, hΓ⟩)
  | impE _ _ ih₁ ih₂ => exact (ih₁ e hΓ) (ih₂ e hΓ)
  | allI _ ih =>
    intro x
    exact ih (Fin.cases x e) (List.forall_mem_map.2 fun b hb => (M.holds_shift b e x).2 (hΓ b hb))
  | allE t _ ih => exact (M.holds_inst _ t e).2 (ih e hΓ (M.eval t e))
  | exI t _ ih => exact ⟨M.eval t e, (M.holds_inst _ t e).1 (ih e hΓ)⟩
  | exE _ _ ih₁ ih₂ =>
    obtain ⟨x, hx⟩ := ih₁ e hΓ
    exact (M.holds_shift _ e x).1 (ih₂ (Fin.cases x e) (List.forall_mem_cons.2 ⟨hx,
      List.forall_mem_map.2 fun b hb => (M.holds_shift b e x).2 (hΓ b hb)⟩))
  | eqRefl _ => rfl
  | eqSubst b σ τ _ _ ih₁ ih₂ =>
    apply (M.holds_subst b τ e).2
    have he : (fun i => M.eval (σ i) e) = (fun i => M.eval (τ i) e) :=
      funext fun i => ih₁ i e hΓ
    rw [← he]
    exact (M.holds_subst b σ e).1 (ih₂ e hΓ)

end TermModel

end LeanProofs.ConciseIPRA
