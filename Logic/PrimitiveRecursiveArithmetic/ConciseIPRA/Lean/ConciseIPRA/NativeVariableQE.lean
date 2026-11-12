import ConciseIPRA.NativeParameter

/-!
# `QE` at a variable or at the numeral one

The rule `QE` of the kernel infers `B(t)` from `Q_y B(y)` and `B(0)` for an
arbitrary term `t`.  The package `Research/deterministic_specialization`
removes the term argument from the use of a clause.  Its counterpart for the
kernel restricts the target of `QE`:

* `VQPrf true` is the kernel in which `QE` is available only at a variable
  (`qEVar`) and at the numeral `1` (`qEOne`), and `vqprf_iff_nprf` proves that
  it derives the same sequents as the kernel;
* `VQPrf false` has `QE` at variables only, and `vqprf_var_incomplete`
  exhibits a sequent that the kernel derives and it does not.

An arbitrary target `t` is recovered by naming it.  Under a fresh alias
`b = t` (`VQPrf.aliasE`, whose discharge uses `QE` at `1` once) the rule is
applied at the variable `b`, and `B(b)` is transported to `B(t)`.  The
transport is the Leibniz rule for the formula `B`, whose proof for a compound
formula needs `QE` at `S z` for its matrix.  So the Leibniz rule and the
general `QE` are proved together, by induction on the formula
(`VQPrf.qELeib`, `VQPrf.leibniz`); the Leibniz rule is stated for the
derivability of the two instances over one context, and no substitution into
a derivation is used.  The calculus is closed under renaming (`VQPrf.ren`),
not under substitution.

For the separation, read every variable as `0` and every `Q` and `D` formula
as true (`NFm.zt`, over the evaluation `Tm.ev` of terms in the natural
numbers).  `QE` at a variable is sound for this reading, since its conclusion
is then its second premise, and `Q_y (sel(y, 0, 1) = 0) ⊢ 0 = 1` is not.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace NFm

theorem subst_up_cases (B : NFm (k + 1)) (ρ : Fin k → Tm n) (t : Tm n) :
    (B.subst (up ρ)).subst (inst t) = B.subst (Fin.cases t ρ) := by
  rw [subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem shift_subst_cases (B : NFm (k + 1)) (t : Tm n) (ρ : Fin k → Tm n) :
    (B.subst (Fin.cases t ρ)).shift
      = B.subst (Fin.cases (Syn.shift t) fun i => Syn.shift (ρ i)) := by
  unfold NFm.shift
  rw [subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Syn.shift]

theorem shift_Q_up (B : NFm (k + 1)) (ρ : Fin k → Tm n) :
    (NFm.Q (B.subst (up ρ))).shift = .Q (B.subst (up fun i => Syn.shift (ρ i))) := by
  unfold NFm.shift
  rw [subst_Q, subst_subst, Syn.up_comp]
  rfl

theorem subst_up_repl (B : NFm (k + 1)) (ρ : Fin k → Tm n) (s : Tm (n + 1)) :
    (B.subst (up ρ)).subst (repl s) = B.subst (Fin.cases s fun i => Syn.shift (ρ i)) := by
  rw [subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem shift_subst_up_zero (B : NFm (k + 1)) (ρ : Fin k → Tm n) :
    ((B.subst (up ρ)).subst (inst zero)).shift
      = B.subst (Fin.cases zero fun i => Syn.shift (ρ i)) := by
  rw [subst_up_cases, shift_subst_cases]
  rfl

end NFm

/-- The kernel with `QE` at a variable, and at the numeral `1` if `c` is
`true`. -/
inductive VQPrf (c : Bool) : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : VQPrf c Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      VQPrf c Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c' a : Tm n) (h : Tm (n + 1)) :
      VQPrf c Γ (.eq (iter (succ c') a h) (Syn.subst (inst (iter c' a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : VQPrf c Γ (.eq s t)) (h₂ : VQPrf c Γ (.eq (Syn.subst (inst s) h) u)) :
      VQPrf c Γ (.eq u (Syn.subst (inst t) h))
  /-- `QE` at a variable. -/
  | qEVar {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (i : Fin n)
      (h₁ : VQPrf c Γ (.Q B)) (h₂ : VQPrf c Γ (B.subst (inst zero))) :
      VQPrf c Γ (B.subst (inst (Syn.var i)))
  /-- `QE` at the numeral `1`. -/
  | qEOne {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (hc : c = true)
      (h₁ : VQPrf c Γ (.Q B)) (h₂ : VQPrf c Γ (B.subst (inst zero))) :
      VQPrf c Γ (B.subst (inst (succ zero)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : VQPrf c Γ (.D B)) (h₂ : VQPrf c (.Q B :: Γ.map NFm.shift) A.shift) : VQPrf c Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : VQPrf c (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      VQPrf c Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : VQPrf c (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      VQPrf c Γ (.Q (.eq s₁ s₂))

namespace VQPrf

variable {c : Bool} {Γ Δ : List (NFm n)} {A : NFm n}

theorem toNPrf (h : VQPrf c Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c' a h => exact .iterSucc c' a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qEVar i _ _ ih₁ ih₂ => exact .qE _ ih₁ ih₂
  | qEOne _ _ _ ih₁ ih₂ => exact .qE _ ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

theorem hyp0 : VQPrf c (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : VQPrf c Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → VQPrf c Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c' a h => intro Δ _; exact .iterSucc c' a h
  | trOne h _ _ ih₁ ih₂ => intro Δ s; exact .trOne h (ih₁ s) (ih₂ s)
  | qEVar i _ _ ih₁ ih₂ => intro Δ s; exact .qEVar i (ih₁ s) (ih₂ s)
  | qEOne hc _ _ ih₁ ih₂ => intro Δ s; exact .qEOne hc (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t _ ih =>
    intro Δ s
    exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : VQPrf c Γ A) : VQPrf c (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : VQPrf c Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    VQPrf c (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ; exact .iterZero _ _
  | iterSucc c' a h =>
    intro m ξ
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ ξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ) h₂
  | qEVar i _ _ ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ ξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qEVar (ξ i) (ih₁ ξ) h₂
  | qEOne hc _ _ ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ ξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qEOne hc (ih₁ ξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ
    have h := ih₂ (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ) h
  | dICase B t _ ih =>
    intro m ξ
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    intro m ξ
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd _ _ h

theorem shift (h : VQPrf c Γ A) : VQPrf c (Γ.map NFm.shift) A.shift := h.ren Fin.succ

theorem cutLift (h : ∀ B ∈ Γ, VQPrf c Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, VQPrf c (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : VQPrf c Γ A) :
    ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, VQPrf c Δ B) → VQPrf c Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c' a h => intro Δ _; exact .iterSucc c' a h
  | trOne h _ _ ih₁ ih₂ => intro Δ hΔ; exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qEVar i _ _ ih₁ ih₂ => intro Δ hΔ; exact .qEVar i (ih₁ hΔ) (ih₂ hΔ)
  | qEOne hc _ _ ih₁ ih₂ => intro Δ hΔ; exact .qEOne hc (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dICase B t _ ih => intro Δ hΔ; exact .dICase B t (ih (cutLift hΔ _))
  | qIInd s₁ s₂ _ ih => intro Δ hΔ; exact .qIInd s₁ s₂ (ih (cutLift hΔ _))

/-! ### Equality -/

theorem eqRefl (t : Tm n) : VQPrf c Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : VQPrf c Γ (.eq s t)) : VQPrf c Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : VQPrf c Γ (.eq s t)) (h₂ : VQPrf c Γ (.eq t u)) :
    VQPrf c Γ (.eq s u) :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

theorem selSucc (c' a b : Tm n) : VQPrf c Γ (.eq (Tm.sel (succ c') a b) b) := by
  have h := VQPrf.iterSucc (c := c) (Γ := Γ) c' a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

/-- Transport in an equation template, with the template and its two instances
named. -/
theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : VQPrf c Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : VQPrf c Γ A) : VQPrf c Γ A' := by
  subst hH hA hA'
  exact .trOne b h₁ (.trOne a h₁ h₂)

/-- The simultaneous Leibniz rule for an equation. -/
theorem leibnizEq (a b : Tm k) (σ σ' : Fin k → Tm n)
    (he : ∀ i, VQPrf c Γ (.eq (σ i) (σ' i)))
    (h : VQPrf c Γ ((NFm.eq a b).subst σ)) : VQPrf c Γ ((NFm.eq a b).subst σ') := by
  have key : ∀ j, j ≤ k →
      VQPrf c Γ ((NFm.eq a b).subst fun i => if i.val < j then σ' i else σ i) := by
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

/-- Introduction of `Q` by cases. -/
theorem qI (B : NFm (n + 1))
    (h : VQPrf c ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : VQPrf c Γ (.Q B) := by
  have hD : VQPrf c Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show VQPrf c (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- Equal substitutions stay equal under a binder. -/
theorem upEq {σ σ' : Fin k → Tm n} (he : ∀ i, VQPrf c Γ (.eq (σ i) (σ' i))) :
    ∀ i, VQPrf c (Γ.map NFm.shift) (.eq (up σ i) (up σ' i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact eqRefl _
  · rw [up_succ, up_succ]
    exact (he j).shift

/-- Equal substitutions extended by equal terms. -/
theorem casesEq {σ σ' : Fin k → Tm n} {s s' : Tm n} (h : VQPrf c Γ (.eq s s'))
    (he : ∀ i, VQPrf c Γ (.eq (σ i) (σ' i))) :
    ∀ i, VQPrf c Γ (.eq ((Fin.cases s σ : Fin (k + 1) → Tm n) i)
      ((Fin.cases s' σ' : Fin (k + 1) → Tm n) i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h
  · simpa only [Fin.cases_succ] using he j

/-! ### The fresh alias, with `QE` at `1` -/

theorem aliasD (a : Tm n) : VQPrf c Γ (.D (NFm.aliasM a)) := by
  refine .dICase _ a ?_
  rw [NFm.aliasM_step]
  exact selSucc _ _ _

/-- **The fresh alias.**  An assumption `b = a` with `b` fresh may be
discharged, by one `QE` at the numeral `1`. -/
theorem aliasE (a : Tm n)
    (h : VQPrf true (.eq (Syn.var 0) (Syn.shift a) :: Γ.map NFm.shift) A.shift) :
    VQPrf true Γ A := by
  refine .dE (aliasD a) ?_
  have k : VQPrf true (.Q (NFm.aliasM a) :: Γ.map NFm.shift)
      ((NFm.aliasM a).subst (inst (succ zero))) := by
    refine .qEOne rfl hyp0 ?_
    rw [NFm.aliasM_inst]
    exact .iterZero _ _
  rw [NFm.aliasM_inst] at k
  refine h.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact .trOne (Syn.var 0) k (selSucc zero _ _)
  · exact .hyp (List.mem_cons_of_mem _ hC)

/-! ### The general `QE` and the Leibniz rule -/

/-- `QE` at an arbitrary target for the matrix `B`, with a change of the
parameters, from the Leibniz rule for `B`. -/
theorem qELeib {B : NFm (k + 1)}
    (ih : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin (k + 1) → Tm n),
      (∀ i, VQPrf true Γ (.eq (σ i) (σ' i))) →
        VQPrf true Γ (B.subst σ) → VQPrf true Γ (B.subst σ'))
    {ρ ρ' : Fin k → Tm n} (he : ∀ i, VQPrf true Γ (.eq (ρ i) (ρ' i))) (t : Tm n)
    (hQ : VQPrf true Γ (.Q (B.subst (up ρ))))
    (h0 : VQPrf true Γ (B.subst (Fin.cases zero ρ'))) :
    VQPrf true Γ (B.subst (Fin.cases t ρ')) := by
  refine aliasE t ?_
  rw [NFm.shift_subst_cases]
  have he' : ∀ i, VQPrf true (.eq (Syn.var 0) (Syn.shift t) :: Γ.map NFm.shift)
      (.eq (Syn.shift (ρ i)) (Syn.shift (ρ' i))) := fun i => (he i).shift.wk
  have hQ' : VQPrf true (.eq (Syn.var 0) (Syn.shift t) :: Γ.map NFm.shift)
      (.Q (B.subst (up fun i => Syn.shift (ρ i)))) := by
    rw [← NFm.shift_Q_up]
    exact hQ.shift.wk
  have h0' : VQPrf true (.eq (Syn.var 0) (Syn.shift t) :: Γ.map NFm.shift)
      (B.subst (Fin.cases zero fun i => Syn.shift (ρ' i))) := by
    have h := h0.shift.wk (B := .eq (Syn.var 0) (Syn.shift t))
    rw [NFm.shift_subst_cases] at h
    exact h
  have base := ih _ _ (casesEq (eqRefl zero) fun i => eqSymm (he' i)) h0'
  have hv := VQPrf.qEVar 0 hQ' (by rw [NFm.subst_up_cases]; exact base)
  rw [NFm.subst_up_cases] at hv
  exact ih _ _ (casesEq hyp0 he') hv

/-- **The simultaneous Leibniz rule**, for the derivability of two instances
over one context. -/
theorem leibniz (A : NFm k) : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin k → Tm n),
    (∀ i, VQPrf true Γ (.eq (σ i) (σ' i))) →
      VQPrf true Γ (A.subst σ) → VQPrf true Γ (A.subst σ') := by
  induction A with
  | eq a b => intro n Γ σ σ' he h; exact leibnizEq a b σ σ' he h
  | Q B ih =>
    intro n Γ σ σ' he h
    rw [NFm.subst_Q] at h ⊢
    refine qI _ ?_
    rw [NFm.subst_up_repl, NFm.shift_subst_up_zero]
    refine qELeib ih (ρ := fun i => Syn.shift (σ i)) (fun i => (he i).shift.wk)
      (succ (Syn.var 0)) ?_ hyp0
    rw [← NFm.shift_Q_up]
    exact h.shift.wk
  | D B ih =>
    intro n Γ σ σ' he h
    rw [NFm.subst_D] at h ⊢
    refine .dE h ?_
    show VQPrf true _ (.D ((B.subst (up (up σ'))).subst (up (up fun i => Syn.var i.succ))))
    refine .dICase _ (Syn.var 0) ?_
    rw [NFm.subst_upup_inst_var, NFm.subst_up_repl, NFm.shift_subst_up_zero]
    refine qELeib ih (ρ := fun i => Syn.shift (up σ i))
      (fun i => ((upEq he i).wk).shift.wk) (succ (Syn.var 0)) ?_ hyp0
    rw [← NFm.shift_Q_up]
    exact .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))

/-- **`QE` at an arbitrary target.** -/
theorem qE {B : NFm (n + 1)} (t : Tm n) (h₁ : VQPrf true Γ (.Q B))
    (h₂ : VQPrf true Γ (B.subst (inst zero))) : VQPrf true Γ (B.subst (inst t)) :=
  qELeib (B := B) (fun σ σ' he h => leibniz B σ σ' he h) (ρ := Syn.var) (ρ' := Syn.var)
    (fun i => eqRefl _) t (by rw [Syn.up_var, NFm.subst_id]; exact h₁) h₂

end VQPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toVQPrf (h : NPrf Γ A) : VQPrf true Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact VQPrf.qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- **`QE` at a variable or at the numeral `1` is enough.** -/
theorem vqprf_iff_nprf : VQPrf true Γ A ↔ NPrf Γ A := ⟨VQPrf.toNPrf, NPrf.toVQPrf⟩

/-! ### Variables alone are not enough -/

namespace Tm

/-- Evaluation of a term in the natural numbers. -/
def ev : {n : ℕ} → Tm n → (Fin n → ℕ) → ℕ
  | _, .var i, ρ => ρ i
  | _, .zero, _ => 0
  | _, .succ t, ρ => t.ev ρ + 1
  | _, .iter c a h, ρ => Nat.rec (a.ev ρ) (fun _ u => h.ev (Fin.cases u ρ)) (c.ev ρ)

theorem ev_ren (t : Tm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m) (ρ : Fin m → ℕ),
    (ren ξ t).ev ρ = t.ev fun i => ρ (ξ i) := by
  induction t with
  | var i => intro m ξ ρ; rfl
  | zero => intro m ξ ρ; rfl
  | succ t ih => intro m ξ ρ; simp only [ren, ev, ih]
  | iter c a h ihc iha ihh =>
    intro m ξ ρ
    simp only [ren, ev, ihc, iha, ihh]
    congr 1
    funext _ u
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem ev_sub (t : Tm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → ℕ),
    (sub σ t).ev ρ = t.ev fun i => (σ i).ev ρ := by
  induction t with
  | var i => intro m σ ρ; rfl
  | zero => intro m σ ρ; rfl
  | succ t ih => intro m σ ρ; simp only [sub, ev, ih]
  | iter c a h ihc iha ihh =>
    intro m σ ρ
    simp only [sub, ev, ihc, iha, ihh]
    congr 1
    funext _ u
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [upS, ev_ren]

theorem ev_subst (σ : Fin n → Tm m) (t : Tm n) (ρ : Fin m → ℕ) :
    (Syn.subst σ t).ev ρ = t.ev fun i => (σ i).ev ρ := ev_sub t σ ρ

end Tm

/-- The reading in which every variable is `0` and every `Q` and `D` formula
is true. -/
def NFm.zt : {n : ℕ} → NFm n → Prop
  | _, .eq s t => s.ev (fun _ => 0) = t.ev (fun _ => 0)
  | _, .Q _ => True
  | _, .D _ => True

theorem NFm.zt_subst_congr (B : NFm k) {σ τ : Fin k → Tm n}
    (h : ∀ i, (σ i).ev (fun _ => 0) = (τ i).ev (fun _ => 0)) :
    (B.subst σ).zt ↔ (B.subst τ).zt := by
  cases B with
  | eq s t =>
    simp only [NFm.subst_eq, NFm.zt, Tm.ev_subst]
    rw [funext h]
  | Q B => exact Iff.rfl
  | D B => exact Iff.rfl

theorem NFm.zt_shift (A : NFm n) : A.shift.zt ↔ A.zt := by
  cases A with
  | eq s t =>
    unfold NFm.shift
    simp only [NFm.subst_eq, NFm.zt, Tm.ev_subst]
    exact Iff.rfl
  | Q B => exact Iff.rfl
  | D B => exact Iff.rfl

/-- `QE` at variables only is sound for the reading `NFm.zt`. -/
theorem VQPrf.zsound (h : VQPrf false Γ A) : (∀ X ∈ Γ, X.zt) → A.zt := by
  induction h with
  | hyp h => intro hΓ; exact hΓ _ h
  | iterZero a h => intro _; rfl
  | iterSucc c a h =>
    intro _
    show (iter (succ c) a h).ev _ = (Syn.subst (inst (iter c a h)) h).ev _
    rw [Tm.ev_subst]
    show h.ev (Fin.cases ((iter c a h).ev fun _ => 0) fun _ => 0) = _
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cases_succ, Syn.inst_succ]
      rfl
  | trOne h _ _ ih₁ ih₂ =>
    intro hΓ
    have e₁ := ih₁ hΓ
    have e₂ := ih₂ hΓ
    simp only [NFm.zt, Tm.ev_subst] at e₁ e₂ ⊢
    rw [← e₂]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact e₁
    · simp
  | @qEVar _ Γ B i _ _ _ ih₂ =>
    intro hΓ
    refine (NFm.zt_subst_congr B fun j => ?_).1 (ih₂ hΓ)
    refine Fin.cases ?_ (fun j' => ?_) j
    · rfl
    · simp
  | qEOne hc _ _ _ _ => exact absurd hc (by decide)
  | dE _ _ _ ih₂ =>
    intro hΓ
    refine (NFm.zt_shift _).1 (ih₂ fun X hX => ?_)
    rcases List.mem_cons.1 hX with rfl | hX
    · trivial
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact (NFm.zt_shift Y).2 (hΓ Y hY)
  | dICase B t _ _ => intro _; trivial
  | qIInd s₁ s₂ _ _ => intro _; trivial

/-- **`QE` at variables alone is not enough.**  The kernel derives `0 = 1`
from `Q_y (sel(y, 0, 1) = 0)`, by `QE` at `1`, and the calculus with `QE` at
variables only does not. -/
theorem vqprf_var_incomplete :
    NPrf [NFm.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero))
      ∧ ¬ VQPrf false [NFm.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero)) := by
  constructor
  · have h := NPrf.qE
      (Γ := ([NFm.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)] : List (NFm 0)))
      (succ zero) NPrf.hyp0 (by
        simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero,
          Tm.subst_succ]
        exact NPrf.selZero _ _)
    simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero,
      Tm.subst_succ] at h
    exact NPrf.eqTrans (NPrf.eqSymm h) (NPrf.selSucc zero zero (succ zero))
  · intro h
    have k := h.zsound fun X hX => by
      rcases List.mem_singleton.1 hX with rfl
      trivial
    exact Nat.succ_ne_zero 0 k.symm

end LeanProofs.ConciseIPRA
