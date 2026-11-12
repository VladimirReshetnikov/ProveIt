import ConciseIPRA.NativeProgressive

/-!
# The uniform rules: structural rules, equality and induction

This module develops the calculus `RPrf` of `NativeProgressive` from the
inside, as far as the recovery of equation induction.

* No rule of `RPrf` looks at a witness, so substitution of terms for the free
  variables of a derivation is a direct induction (`RPrf.subst`), and so are
  weakening and cut.
* Reflexivity, symmetry, transitivity, congruence, the transport rule of the
  kernel and the simultaneous Leibniz rule for equations follow from transport
  in an equation template and the first computation equation.
* **Equation induction** (`RPrf.eqInd`): from `E(0)` and `E(z) ⊢ E(S z)` infer
  `E(u)`.  The introduction at a literal equation gives `D_{x,y} E(y)` with `x`
  unused, its elimination gives the progressive `Q_y E(y)`, and the
  elimination of `Q` with the source `0` gives `E(I(0, u; v.S v))`, which is
  `E(u)` by the first computation equation.  No property of addition is used.
* `RPrf.addOne`: `I(z, 1; v.S v) = S z`, by that induction.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

theorem NFm.eta_subst {k k' : ℕ} (B : NFm k) (τ : Fin k → Tm k') (σ : Fin n → Tm m)
    (a : Tm n) : Syn.subst σ (NFm.eta B a) = NFm.eta (B.subst τ) (Syn.subst σ a) := by
  unfold NFm.eta
  rw [NFm.isEq_subst]
  cases B.isEq <;> rfl

theorem NFm.subst_repl_up_comm (A : NFm (n + 1)) (d : Tm (n + 1)) (σ : Fin n → Tm m) :
    (A.subst (repl d)).subst (up σ) = (A.subst (up σ)).subst (repl (Syn.subst (up σ) d)) := by
  rw [NFm.subst_subst, NFm.subst_subst]
  refine A.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [repl_succ, Syn.subst_var, up_succ, Syn.subst_repl_shift]

namespace RPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

theorem hyp0 : RPrf (A :: Γ) A := .hyp List.mem_cons_self

/-! ### Structural rules -/

theorem weaken (h : RPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → RPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => intro Δ s; exact .trEq p q (ih₁ s) (ih₂ s)
  | qE a c _ _ ih₁ ih₂ => intro Δ s; exact .qE a c (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : RPrf Γ A) : RPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Substitution of terms for the free variables of a derivation. -/
theorem subst (h : RPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    RPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m σ; exact .iterZero _ _
  | iterSucc c a h =>
    intro m σ
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trEq p q _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trEq _ _ (ih₁ σ) h₂
  | @qE _ Γ B a c _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst, NFm.eta_subst B (up σ) σ a] at h₂
    rw [NFm.subst_inst, Tm.subst_add, NFm.eta_subst B (up σ) σ a]
    exact .qE _ _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | @dI _ Γ B t _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_up_comm _ (NFm.eta B (Syn.var 0)),
      NFm.subst_repl_succ, NFm.subst_up_inst,
      NFm.eta_subst B (up (up σ)) (up σ) (Syn.var 0)] at h
    simp only [Syn.subst_var, Syn.up_zero] at h
    exact .dI _ _ h

/-- A derivation may be moved under a fresh variable. -/
theorem shift (h : RPrf Γ A) : RPrf (Γ.map NFm.shift) A.shift := h.subst _

theorem cutLift (h : ∀ B ∈ Γ, RPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, RPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : RPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, RPrf Δ B) → RPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => intro Δ hΔ; exact .trEq p q (ih₁ hΔ) (ih₂ hΔ)
  | qE a c _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE a c (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dI B t _ ih => intro Δ hΔ; exact .dI B t (ih (cutLift hΔ _))

/-- Cut of one hypothesis. -/
theorem cut1 {B : NFm n} (h₁ : RPrf Γ B) (h₂ : RPrf (B :: Γ) A) : RPrf Γ A := by
  refine h₂.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact h₁
  · exact .hyp hC

/-! ### Equality -/

/-- Transport in an equation template, with the template and its two instances
named. -/
theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : RPrf Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : RPrf Γ A) : RPrf Γ A' := by
  subst hH hA hA'
  exact .trEq a b h₁ h₂

theorem eqRefl (t : Tm n) : RPrf Γ (.eq t t) :=
  trE (.eq (Syn.var 0) (Syn.shift t)) rfl (.iterZero t (Syn.var 0)) (by simp) (by simp)
    (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : RPrf Γ (.eq s t)) : RPrf Γ (.eq t s) :=
  trE (.eq (Syn.var 0) (Syn.shift s)) rfl h (by simp) (by simp) (eqRefl s)

theorem eqTrans {s t u : Tm n} (h₁ : RPrf Γ (.eq s t)) (h₂ : RPrf Γ (.eq t u)) :
    RPrf Γ (.eq s u) :=
  trE (.eq (Syn.shift s) (Syn.var 0)) rfl h₂ (by simp) (by simp) h₁

/-- Replacement of equals inside a term. -/
theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : RPrf Γ (.eq s t)) :
    RPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  trE (A := .eq (Syn.subst (inst s) h) (Syn.subst (inst s) h))
    (.eq (Syn.shift (Syn.subst (inst s) h)) h) rfl e (by simp) (by simp) (eqRefl _)

/-- The transport rule of the kernel. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : RPrf Γ (.eq s t))
    (h₂ : RPrf Γ (.eq (Syn.subst (inst s) h) u)) : RPrf Γ (.eq u (Syn.subst (inst t) h)) :=
  eqTrans (eqSymm h₂) (eqCongr h h₁)

/-- The simultaneous Leibniz rule for an equation. -/
theorem leibnizEq (a b : Tm k) (σ σ' : Fin k → Tm n) (he : ∀ i, RPrf Γ (.eq (σ i) (σ' i)))
    (h : RPrf Γ ((NFm.eq a b).subst σ)) : RPrf Γ ((NFm.eq a b).subst σ') := by
  have key : ∀ j, j ≤ k →
      RPrf Γ ((NFm.eq a b).subst fun i => if i.val < j then σ' i else σ i) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hj' := ih (Nat.le_of_succ_le hj)
      refine trE ((NFm.eq a b).subst fun i => if i.val = j then Syn.var 0
          else Syn.shift (if i.val < j then σ' i else σ i)) rfl (he ⟨j, hj⟩) ?_ ?_ hj'
      · rw [NFm.subst_subst]
        refine NFm.subst_ext _ fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · simp [hi]
      · rw [NFm.subst_subst]
        refine NFm.subst_ext _ fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · have hlt : i.val < j + 1 ↔ i.val < j := by omega
          simp [hi, hlt]
  have h' := key k le_rfl
  simpa using h'

/-! ### Equation induction -/

/-- **Equation induction in the uniform calculus.**  From `E(0)` and
`E(z) ⊢ E(S z)` with `z` fresh, infer `E(u)`. -/
theorem eqInd (s t : Tm (n + 1)) (u : Tm n) (h0 : RPrf Γ ((NFm.eq s t).subst (inst zero)))
    (hS : RPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    RPrf Γ ((NFm.eq s t).subst (inst u)) := by
  have hD : RPrf Γ (.D ((NFm.eq s t).subst (up fun i => Syn.var i.succ))) := by
    refine .dI _ zero ?_
    rw [NFm.subst_dummy_inst,
      show NFm.eta ((NFm.eq s t).subst (up fun i => Syn.var i.succ))
        (Syn.var 0 : Tm (n + 1)) = Syn.var 0 from rfl, NFm.subst_repl_var]
    exact hS
  refine .dE hD ?_
  have h0' : RPrf (.Q ((NFm.eq s t).subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
      (((NFm.eq s t).subst (up fun i => Syn.var i.succ)).subst
        (inst (NFm.eta ((NFm.eq s t).subst (up fun i => Syn.var i.succ))
          (zero : Tm (n + 1))))) := by
    rw [show NFm.eta ((NFm.eq s t).subst (up fun i => Syn.var i.succ)) (zero : Tm (n + 1))
        = zero from rfl, NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero]
    exact h0.shift.wk
  have q := RPrf.qE zero (Syn.shift u) hyp0 h0'
  rw [show NFm.eta ((NFm.eq s t).subst (up fun i => Syn.var i.succ)) (zero : Tm (n + 1))
      = zero from rfl, NFm.subst_dummy_up_inst] at q
  rw [NFm.shift_subst_inst]
  exact trE ((NFm.eq s t).subst (up fun i => Syn.var i.succ)) rfl
    (.iterZero (Syn.shift u) (succ (Syn.var 0))) (NFm.subst_dummy_up_inst _ _)
    (NFm.subst_dummy_up_inst _ _) q

/-- `I(z, 1; v. S v) = S z`. -/
theorem addOne (z : Tm n) : RPrf Γ (.eq (Tm.add (succ zero) z) (succ z)) := by
  have k := eqInd (Γ := Γ) (Tm.add (succ zero) (Syn.var 0)) (succ (Syn.var 0)) z
    (RPrf.iterZero (succ zero) (succ (Syn.var 0)))
    (eqTrans (RPrf.iterSucc (Syn.var 0) (succ zero) (succ (Syn.var 0)))
      (eqCongr (succ (Syn.var 0)) hyp0))
  exact k

end RPrf

end LeanProofs.ConciseIPRA
