import ConciseIPRA.NativeEq

/-!
# Substitution at the discharge of a witness

The package `Research/substitutive_discharge` fuses equality transport with the
elimination of `D` into one rule,

  from `D_{x,y} B`, and from `s = t` and `F(s)` in the context opened at a
  fresh `b`, infer `F(t)`, provided `F(t)` does not mention `b`.

The template `F` has its own variable; `s`, `t` and `F` may mention `b`.

`SDPrf` is the kernel with this rule in place of both transport and `DE`:
seven rules, of which only one concerns equality or the elimination of a
binder besides `QE`.  `sdprf_iff_nprf` proves that it derives the same sequents
as the kernel.

* The discharge is `DE` followed by transport in a formula.
* Conversely, with the closed theorem `D_{x,y} (I(0, 0; u.u) = 0)`, proved by
  cases from a computation, the discharge whose opened context is not used is
  transport in an arbitrary formula (`SDPrf.tr`).  Transporting
  `I(0, a; u.u) = a` along itself gives `a = a`, and symmetry and the crossed
  transport of the kernel follow.  A constant template gives `DE`
  (`SDPrf.dE`), with a computation as its equation.

Every rule is stable under substitution, so the calculus has substitution by a
direct induction (`SDPrf.subst`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The kernel with substitutive discharge in place of transport and `DE`. -/
inductive SDPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : SDPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      SDPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      SDPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : SDPrf Γ (.Q B)) (h₂ : SDPrf Γ (B.subst (inst zero))) : SDPrf Γ (B.subst (inst t))
  /-- Substitutive discharge: from `D_{x,y} B`, and from `s = t` and `F(s)` in
  the context opened at a fresh `b`, infer `F(t)`, which does not mention
  `b`. -/
  | sd {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 2))
      {s t : Tm (n + 1)} (h₁ : SDPrf Γ (.D B))
      (h₂ : SDPrf (.Q B :: Γ.map NFm.shift) (.eq s t))
      (h₃ : SDPrf (.Q B :: Γ.map NFm.shift) (F.subst (inst s)))
      (hA : F.subst (inst t) = A.shift) : SDPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : SDPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      SDPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : SDPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      SDPrf Γ (.Q (.eq s₁ s₂))

namespace SDPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

/-- The discharge is `DE` followed by transport in a formula. -/
theorem toNPrf (h : SDPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | sd F _ _ _ hA ih₁ ih₂ ih₃ => exact .dE ih₁ (hA ▸ NPrf.tr F ih₂ ih₃)
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

theorem weaken (h : SDPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → SDPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | sd F _ _ _ hA ih₁ ih₂ ih₃ =>
    intro Δ s
    exact .sd F (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
      (ih₃ (List.cons_subset_cons _ (List.map_subset _ s))) hA
  | dICase B t _ ih =>
    intro Δ s
    exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : SDPrf Γ A) : SDPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Substitution in a derivation. -/
theorem subst (h : SDPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    SDPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m σ; exact .iterZero _ _
  | iterSucc c a h =>
    intro m σ
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | qE t _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | @sd _ Γ B A F s t _ _ _ hA ih₁ ih₂ ih₃ =>
    intro m σ
    have h₂ := ih₂ (up σ)
    have h₃ := ih₃ (up σ)
    rw [List.map_cons, NFm.map_shift_subst] at h₂ h₃
    rw [NFm.subst_inst] at h₃
    refine .sd (F.subst (up (up σ))) (ih₁ σ) h₂ h₃ ?_
    rw [← NFm.subst_inst, hA, NFm.shift_subst_up]
  | dICase B t _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd (Syn.subst (up σ) s₁) (Syn.subst (up σ) s₂) h

theorem shift (h : SDPrf Γ A) : SDPrf (Γ.map NFm.shift) A.shift := h.subst _

/-! ### Transport and `DE` from the discharge -/

/-- A closed theorem to open: `D_{x,y} (I(0, 0; u.u) = 0)`, by cases from a
computation. -/
theorem dummyD : SDPrf Γ (.D (.eq (iter zero zero (Syn.var 0)) zero)) := by
  refine .dICase _ zero ?_
  exact .iterZero zero (Syn.var 0)

/-- **Transport in a formula**, by a discharge whose opened context is not
used. -/
theorem tr (G : NFm (n + 1)) {s t : Tm n} (e : SDPrf Γ (.eq s t))
    (k : SDPrf Γ (G.subst (inst s))) : SDPrf Γ (G.subst (inst t)) := by
  have e' : ∀ x : Tm n, (G.subst (inst x)).shift
      = (G.subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift x)) :=
    fun x => NFm.subst_inst G _ x
  refine .sd (G.subst (up fun i => Syn.var i.succ)) (s := Syn.shift s) (t := Syn.shift t)
    dummyD e.shift.wk ?_ (e' t).symm
  rw [← e' s]
  exact k.shift.wk

theorem eqRefl (a : Tm n) : SDPrf Γ (.eq a a) := by
  have h := tr (Γ := Γ) (.eq (Syn.var 0) (Syn.shift a)) (.iterZero a (Syn.var 0)) (by
    rw [NFm.subst_eq, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact .iterZero a (Syn.var 0))
  rwa [NFm.subst_eq, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h

theorem eqSymm {s t : Tm n} (e : SDPrf Γ (.eq s t)) : SDPrf Γ (.eq t s) := by
  have h := tr (.eq (Syn.var 0) (Syn.shift s)) e (by
    rw [NFm.subst_eq, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact eqRefl s)
  rwa [NFm.subst_eq, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h

/-- The transport of the kernel. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (e : SDPrf Γ (.eq s t))
    (k : SDPrf Γ (.eq (Syn.subst (inst s) h) u)) : SDPrf Γ (.eq u (Syn.subst (inst t) h)) := by
  have r := tr (.eq (Syn.shift u) h) e (by
    rw [NFm.subst_eq, Syn.subst_inst_shift]
    exact eqSymm k)
  rwa [NFm.subst_eq, Syn.subst_inst_shift] at r

/-- `DE`, by a discharge with a constant template and a computation as its
equation. -/
theorem dE {B : NFm (n + 2)} (h₁ : SDPrf Γ (.D B))
    (h₂ : SDPrf (.Q B :: Γ.map NFm.shift) A.shift) : SDPrf Γ A := by
  refine .sd A.shift.shift (s := iter zero zero (Syn.var 0)) (t := zero) h₁
    (.iterZero zero (Syn.var 0)) ?_ (NFm.subst_inst_shift _ _)
  rw [NFm.subst_inst_shift]
  exact h₂

end SDPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toSDPrf (h : NPrf Γ A) : SDPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact SDPrf.trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact SDPrf.dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- **Substitutive discharge is enough.**  The kernel with one rule in place of
transport and `DE` derives the same sequents. -/
theorem sdprf_iff_nprf : SDPrf Γ A ↔ NPrf Γ A := ⟨SDPrf.toNPrf, NPrf.toSDPrf⟩

end LeanProofs.ConciseIPRA
