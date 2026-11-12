import ConciseIPRA.NativeEq

/-!
# Selector formulas in the native scalar core

The native calculus has no connectives.  A case distinction on a term `v` is
therefore pushed inside a formula, down to its equations:

* `NFm.selEq v s t B` is the equation `s = t` when `v = 0` and the formula `B`
  when `v` is a successor;
* `NFm.gate v A = selEq v 0 0 A` is trivially true when `v = 0` and is `A`
  when `v` is a successor;
* `NFm.sel v A B` is `A` when `v = 0` and `B` when `v` is a successor.

Under a binder of `B` the equation `s = t` is guarded by the bound variable, so
that the instance of the binder at zero is trivial and the binder collapses to
`s = t` again (`NEquiv.qSel`, `NEquiv.dSel`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

namespace NFm

/-- The equation `s = t` at `v = 0`, the formula `B` at a successor. -/
def selEq : {n : ℕ} → Tm n → Tm n → Tm n → NFm n → NFm n
  | _, v, s, t, eq u w => eq (Tm.sel v s u) (Tm.sel v t w)
  | _, v, s, t, Q B =>
    Q (selEq (Syn.shift v) (Tm.sel (Syn.var 0) zero (Syn.shift s))
      (Tm.sel (Syn.var 0) zero (Syn.shift t)) B)
  | _, v, s, t, D B =>
    D (selEq (Syn.shift (Syn.shift v)) (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift s)))
      (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift t))) B)

theorem selEq_subst (B : NFm n) : ∀ {m : ℕ} (v s t : Tm n) (σ : Fin n → Tm m),
    (selEq v s t B).subst σ
      = selEq (Syn.subst σ v) (Syn.subst σ s) (Syn.subst σ t) (B.subst σ) := by
  induction B with
  | eq u w => intro m v s t σ; simp only [selEq, subst_eq, Tm.subst_sel]
  | Q B ih =>
    intro m v s t σ
    simp only [selEq, subst_Q, ih, Tm.subst_sel, Syn.subst_var, Syn.up_zero,
      Syn.subst_up_shift, Tm.subst_zero]
  | D B ih =>
    intro m v s t σ
    simp only [selEq, subst_D, ih, Tm.subst_sel, Syn.subst_var, Syn.up_zero,
      Syn.subst_up_shift, Tm.subst_zero]

/-- The gate: trivially true at `v = 0`, the formula `A` at a successor. -/
def gate (v : Tm n) (A : NFm n) : NFm n := selEq v zero zero A

theorem gate_subst (v : Tm n) (A : NFm n) (σ : Fin n → Tm m) :
    (gate v A).subst σ = gate (Syn.subst σ v) (A.subst σ) :=
  selEq_subst A v zero zero σ

theorem gate_shift_inst (A : NFm n) (t : Tm n) :
    (gate (Syn.var 0) A.shift).subst (inst t) = gate t A := by
  rw [gate_subst, Syn.subst_var, Syn.inst_zero, subst_inst_shift]

theorem gate_shift_repl (A : NFm n) (t : Tm (n + 1)) :
    (gate (Syn.var 0) A.shift).subst (repl t) = gate t A.shift := by
  rw [gate_subst, Syn.subst_var, Syn.repl_zero, subst_repl_shift]

/-- The formula `A` at `v = 0`, the formula `B` at a successor. -/
def sel : {n : ℕ} → Tm n → NFm n → NFm n → NFm n
  | _, v, eq s t, B => selEq v s t B
  | _, v, Q A, B => Q (sel (Syn.shift v) A (gate (Syn.var 0) B.shift))
  | _, v, D A, B => D (sel (Syn.shift (Syn.shift v)) A (gate (Syn.var 0) B.shift.shift))

theorem sel_subst (A : NFm n) : ∀ {m : ℕ} (v : Tm n) (B : NFm n) (σ : Fin n → Tm m),
    (sel v A B).subst σ = sel (Syn.subst σ v) (A.subst σ) (B.subst σ) := by
  induction A with
  | eq s t => intro m v B σ; exact selEq_subst B v s t σ
  | Q A ih =>
    intro m v B σ
    simp only [sel, subst_Q, ih, gate_subst, Syn.subst_var, Syn.up_zero,
      Syn.subst_up_shift, shift_subst_up]
  | D A ih =>
    intro m v B σ
    simp only [sel, subst_D, ih, gate_subst, Syn.subst_var, Syn.up_zero,
      Syn.subst_up_shift, shift_subst_up]

theorem sel_shift_inst (A B : NFm n) (t : Tm n) :
    (sel (Syn.var 0) A.shift B.shift).subst (inst t) = sel t A B := by
  rw [sel_subst, Syn.subst_var, Syn.inst_zero, subst_inst_shift, subst_inst_shift]

theorem sel_shift_repl (A B : NFm n) (t : Tm (n + 1)) :
    (sel (Syn.var 0) A.shift B.shift).subst (repl t) = sel t A.shift B.shift := by
  rw [sel_subst, Syn.subst_var, Syn.repl_zero, subst_repl_shift, subst_repl_shift]

end NFm

namespace NEquiv

/-- Equations with provably equal sides are interderivable. -/
theorem eqs {s s' t t' : Tm n} (h₁ : ∀ {Γ : List (NFm n)}, NPrf Γ (.eq s s'))
    (h₂ : ∀ {Γ : List (NFm n)}, NPrf Γ (.eq t t')) : NEquiv (.eq s t) (.eq s' t') :=
  ⟨NPrf.eqTrans (NPrf.eqTrans (NPrf.eqSymm h₁) NPrf.hyp0) h₂,
    NPrf.eqTrans (NPrf.eqTrans h₁ NPrf.hyp0) (NPrf.eqSymm h₂)⟩

/-- `Q_y (sel(y, 0, s) = sel(y, 0, t))` is interderivable with `s = t`. -/
theorem qSel (s t : Tm n) :
    NEquiv (.Q (.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
      (Tm.sel (Syn.var 0) zero (Syn.shift t)))) (.eq s t) := by
  constructor
  · have h0 : NPrf [NFm.Q (.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
          (Tm.sel (Syn.var 0) zero (Syn.shift t)))]
        ((NFm.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
          (Tm.sel (Syn.var 0) zero (Syn.shift t))).subst (inst zero)) := by
      simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, Tm.subst_zero]
      exact NPrf.eqTrans (NPrf.selZero _ _) (NPrf.eqSymm (NPrf.selZero _ _))
    have h1 := NPrf.qE (succ zero) NPrf.hyp0 h0
    simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, Tm.subst_zero] at h1
    exact NPrf.eqTrans (NPrf.eqTrans (NPrf.eqSymm (NPrf.selSucc _ _ _)) h1)
      (NPrf.selSucc _ _ _)
  · refine .qIProg _ _ ?_
    simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero,
      Syn.subst_repl_shift, Tm.subst_zero]
    have h : NPrf (NFm.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
          (Tm.sel (Syn.var 0) zero (Syn.shift t)) :: [NFm.eq s t].map NFm.shift)
        (.eq (Syn.shift s) (Syn.shift t)) :=
      .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    exact NPrf.eqTrans (NPrf.eqTrans (NPrf.selSucc _ _ _) h)
      (NPrf.eqSymm (NPrf.selSucc _ _ _))

/-- A `D` whose witness variable is a dummy is a `Q`. -/
theorem dDummy (B : NFm (n + 1)) :
    NEquiv (.D (B.subst (up (fun i => Syn.var i.succ)))) (.Q B) := by
  constructor
  · refine .dE NPrf.hyp0 ?_
    show NPrf (.Q (B.subst (up (fun i => Syn.var i.succ))) :: _)
      (.Q (B.subst (up (fun i => Syn.var i.succ))))
    exact NPrf.hyp0
  · refine .dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact qStep (refl B)

/-- `D_{x,y} (sel(y, 0, s) = sel(y, 0, t))` is interderivable with `s = t`. -/
theorem dSel (s t : Tm n) :
    NEquiv (.D (.eq (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift s)))
      (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift t))))) (.eq s t) := by
  have e := dDummy (.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
    (Tm.sel (Syn.var 0) zero (Syn.shift t)))
  simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.up_zero, Syn.subst_up_shift,
    Tm.subst_zero] at e
  exact e.trans (qSel s t)

/-- At zero, `selEq` is its equation. -/
theorem selEq_zero (B : NFm n) : ∀ s t : Tm n, NEquiv (NFm.selEq zero s t B) (.eq s t) := by
  induction B with
  | eq u w => intro s t; exact eqs (NPrf.selZero _ _) (NPrf.selZero _ _)
  | Q B ih =>
    intro s t
    show NEquiv (.Q (NFm.selEq zero (Tm.sel (Syn.var 0) zero (Syn.shift s))
      (Tm.sel (Syn.var 0) zero (Syn.shift t)) B)) (.eq s t)
    exact (NEquiv.Q (ih _ _)).trans (qSel s t)
  | D B ih =>
    intro s t
    show NEquiv (.D (NFm.selEq zero (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift s)))
      (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift t))) B)) (.eq s t)
    exact (NEquiv.D (ih _ _)).trans (dSel s t)

/-- At a successor, `selEq` is its formula. -/
theorem selEq_succ (B : NFm n) : ∀ v s t : Tm n, NEquiv (NFm.selEq (succ v) s t B) B := by
  induction B with
  | eq u w => intro v s t; exact eqs (NPrf.selSucc _ _ _) (NPrf.selSucc _ _ _)
  | Q B ih =>
    intro v s t
    show NEquiv (.Q (NFm.selEq (succ (Syn.shift v)) _ _ B)) (.Q B)
    exact NEquiv.Q (ih _ _ _)
  | D B ih =>
    intro v s t
    show NEquiv (.D (NFm.selEq (succ (Syn.shift (Syn.shift v))) _ _ B)) (.D B)
    exact NEquiv.D (ih _ _ _)

/-- The gate is open at zero. -/
theorem gateZero (A : NFm n) {Γ : List (NFm n)} : NPrf Γ (NFm.gate zero A) :=
  (selEq_zero A zero zero).mpr (NPrf.eqRefl zero)

theorem gate_succ (v : Tm n) (A : NFm n) : NEquiv (NFm.gate (succ v) A) A :=
  selEq_succ A v zero zero

/-- `Q_y gate(y, A)` is interderivable with `A`. -/
theorem qGate (A : NFm n) : NEquiv (.Q (NFm.gate (Syn.var 0) A.shift)) A := by
  constructor
  · have h := NPrf.qE (Γ := [NFm.Q (NFm.gate (Syn.var 0) A.shift)]) (succ zero) NPrf.hyp0
      (by rw [NFm.gate_shift_inst]; exact gateZero A)
    rw [NFm.gate_shift_inst] at h
    exact (gate_succ zero A).mp h
  · refine .qI _ ?_
    rw [NFm.gate_shift_repl]
    exact (gate_succ _ _).mpr (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))

/-- `D_{x,y} gate(y, A)` is interderivable with `A`. -/
theorem dGate (A : NFm n) : NEquiv (.D (NFm.gate (Syn.var 0) A.shift.shift)) A := by
  have e := dDummy (NFm.gate (Syn.var 0) A.shift)
  rw [NFm.gate_subst, Syn.subst_var, Syn.up_zero, NFm.shift_subst_up] at e
  exact e.trans (qGate A)

/-- At zero, `sel` is its first formula. -/
theorem sel_zero (A : NFm n) : ∀ B : NFm n, NEquiv (NFm.sel zero A B) A := by
  induction A with
  | eq s t => intro B; exact selEq_zero B s t
  | Q A ih =>
    intro B
    show NEquiv (.Q (NFm.sel zero A _)) (.Q A)
    exact NEquiv.Q (ih _)
  | D A ih =>
    intro B
    show NEquiv (.D (NFm.sel zero A _)) (.D A)
    exact NEquiv.D (ih _)

/-- At a successor, `sel` is its second formula. -/
theorem sel_succ (A : NFm n) : ∀ (v : Tm n) (B : NFm n), NEquiv (NFm.sel (succ v) A B) B := by
  induction A with
  | eq s t => intro v B; exact selEq_succ B v s t
  | Q A ih =>
    intro v B
    show NEquiv (.Q (NFm.sel (succ (Syn.shift v)) A (NFm.gate (Syn.var 0) B.shift))) B
    exact (NEquiv.Q (ih _ _)).trans (qGate B)
  | D A ih =>
    intro v B
    show NEquiv (.D (NFm.sel (succ (Syn.shift (Syn.shift v))) A
      (NFm.gate (Syn.var 0) B.shift.shift))) B
    exact (NEquiv.D (ih _ _)).trans (dGate B)

end NEquiv

end LeanProofs.ConciseIPRA
