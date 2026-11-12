import ConciseIPRA.Native
import ConciseIPRA.Lindenbaum

/-!
# Structural properties of the native scalar core

The native calculus has no structural rules.  This module proves that the
usual ones are admissible:

* `NPrf.weaken`: weakening of the context;
* `NPrf.subst`: substitution of terms for the free variables of a derivation;
* `NPrf.cut`: simultaneous replacement of hypotheses by derivations.

It also derives an introduction rule for the quantifier `Q`,

  `NPrf.qI`: from `B(0) ⊢ B(S z)` with `z` fresh, infer `Q_y B(y)`,

by introducing `D_{x,y} B(y)` with a dummy `x` and eliminating it at once.
Together with the rule `qE` this gives proof by numerical cases
(`NPrf.cases`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

namespace Syn

variable {T : ℕ → Type} [Syn T]

/-- Substitution commutes with instantiation of the first variable. -/
theorem subst_subst_inst (σ : Fin n → T m) (t : T n) (h : T (n + 1)) :
    subst σ (subst (inst t) h) = subst (inst (subst σ t)) (subst (up σ) h) := by
  rw [subst_subst, subst_subst, inst_comp_up]

end Syn

namespace NFm

theorem subst_ext (A : NFm n) {σ τ : Fin n → Tm m} (h : ∀ i, σ i = τ i) :
    A.subst σ = A.subst τ :=
  congrArg A.subst (funext h)

theorem subst_id (A : NFm n) : A.subst Syn.var = A := by
  induction A with
  | eq s t => simp
  | Q B ih => rw [subst_Q, up_var, ih]
  | D B ih => rw [subst_D, up_var, up_var, ih]

theorem subst_eq_self (A : NFm n) {σ : Fin n → Tm n} (h : ∀ i, σ i = Syn.var i) :
    A.subst σ = A :=
  (A.subst_ext h).trans A.subst_id

theorem subst_subst (A : NFm n) : ∀ {m k : ℕ} (σ : Fin n → Tm m) (τ : Fin m → Tm k),
    (A.subst σ).subst τ = A.subst (fun i => Syn.subst τ (σ i)) := by
  induction A with intro m k σ τ
  | eq s t => simp [Syn.subst_subst]
  | Q B ih => rw [subst_Q, subst_Q, ih, up_comp, subst_Q]
  | D B ih => rw [subst_D, subst_D, ih, up_comp, up_comp, subst_D]

theorem shift_subst_up (A : NFm n) (σ : Fin n → Tm m) :
    A.shift.subst (up σ) = (A.subst σ).shift := by
  unfold NFm.shift
  rw [subst_subst, subst_subst]
  exact A.subst_ext fun i => by simp [Syn.shift]

@[simp] theorem subst_inst_shift (A : NFm n) (t : Tm n) : A.shift.subst (inst t) = A := by
  unfold NFm.shift
  rw [subst_subst]
  exact A.subst_eq_self fun i => by simp

theorem subst_inst (A : NFm (n + 1)) (σ : Fin n → Tm m) (t : Tm n) :
    (A.subst (inst t)).subst σ = (A.subst (up σ)).subst (inst (Syn.subst σ t)) := by
  rw [subst_subst, subst_subst, inst_comp_up]

/-- Substitution commutes with instantiation of the second variable. -/
theorem subst_up_inst (B : NFm (n + 2)) (σ : Fin n → Tm m) (t : Tm n) :
    (B.subst (up (inst t))).subst (up σ)
      = (B.subst (up (up σ))).subst (up (inst (Syn.subst σ t))) := by
  rw [subst_subst, subst_subst, up_comp, up_comp, inst_comp_up]

/-- Substitution commutes with the successor step of a bound variable. -/
theorem subst_repl_succ (A : NFm (n + 1)) (σ : Fin n → Tm m) :
    (A.subst (repl (succ (Syn.var 0)))).subst (up σ)
      = (A.subst (up σ)).subst (repl (succ (Syn.var 0))) := by
  rw [subst_subst, subst_subst]
  refine A.subst_ext (Fin.cases ?_ fun j => ?_)
  · simp
  · rw [repl_succ, Syn.subst_var, up_succ, subst_repl_shift]

/-- A dummy second variable disappears when it is instantiated. -/
theorem subst_dummy_inst (B : NFm (n + 1)) (t : Tm n) :
    (B.subst (up (fun i => Syn.var i.succ))).subst (up (inst t)) = B := by
  rw [subst_subst]
  refine B.subst_eq_self (Fin.cases ?_ fun j => ?_) <;> simp

theorem map_shift_subst (Γ : List (NFm n)) (σ : Fin n → Tm m) :
    (Γ.map NFm.shift).map (fun A => A.subst (up σ))
      = (Γ.map (fun A => A.subst σ)).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => shift_subst_up A σ

end NFm

namespace NPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

theorem hyp0 : NPrf (A :: Γ) A := .hyp List.mem_cons_self

/-- Weakening. -/
theorem weaken (h : NPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → NPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ s; exact .trOne h (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t _ ih =>
    intro Δ s
    exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : NPrf Γ A) : NPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

theorem ofNil (h : NPrf [] A) : NPrf Γ A := h.weaken (List.nil_subset _)

/-- Substitution of terms for the free variables of a derivation. -/
theorem subst (h : NPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    NPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with intro m σ
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero _ _
  | iterSucc c a h =>
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ σ) h₂
  | qE t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | dICase B t _ ih =>
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd (Syn.subst (up σ) s₁) (Syn.subst (up σ) s₂) h

/-- A derivation may be moved under a fresh variable. -/
theorem shift (h : NPrf Γ A) : NPrf (Γ.map NFm.shift) A.shift :=
  h.subst _

theorem cutLift (h : ∀ B ∈ Γ, NPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, NPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : NPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, NPrf Δ B) → NPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ hΔ; exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dICase B t _ ih => intro Δ hΔ; exact .dICase B t (ih (cutLift hΔ _))
  | qIInd s₁ s₂ _ ih => intro Δ hΔ; exact .qIInd s₁ s₂ (ih (cutLift hΔ _))

/-- Cut of one hypothesis. -/
theorem cut1 {B : NFm n} (h₁ : NPrf Γ B) (h₂ : NPrf (B :: Γ) A) : NPrf Γ A := by
  refine h₂.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact h₁
  · exact .hyp hC

/-- Introduction of `Q`: from `B(0) ⊢ B(S z)` with `z` fresh, infer `Q_y B(y)`. -/
theorem qI (B : NFm (n + 1))
    (h : NPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : NPrf Γ (.Q B) := by
  have hD : NPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show NPrf (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- Numerical cases: `B(t)` follows from `B(0)` and `B(0) ⊢ B(S z)`. -/
theorem cases (B : NFm (n + 1)) (t : Tm n) (h0 : NPrf Γ (B.subst (inst zero)))
    (hS : NPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : NPrf Γ (B.subst (inst t)) :=
  .qE t (qI B hS) h0

end NPrf

end LeanProofs.ConciseIPRA
