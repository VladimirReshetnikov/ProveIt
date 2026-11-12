import ConciseIPRA.NativeGate

/-!
# The logical connectives as native formulas

The native scalar core has no connectives.  This module defines them as
abbreviations and derives their natural deduction rules:

* `NFm.bot` is `0 = 1`;
* `NFm.imp A B` is `Q_y sel(y, A, B)`;
* `NFm.and A B` is `Q_y gate(y, sel(par y, A, B))`, with `par` the parity;
* `NFm.ex A` is `D_{x,y} gate(y, A(x))`;
* `NFm.or A B` is `ex_v sel(v, A, B)`;
* `NFm.all A` is `and A(0) (Q_y A(y))`.

Each rule of intuitionistic natural deduction is derivable for these
abbreviations (`NPrf.botE`, `NPrf.impI`, ..., `NPrf.allE`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

/-- The parity iterator `I(y, 0; u. sel(u, 1, 0))`. -/
def Tm.npar (y : Tm n) : Tm n := Tm.iter y Tm.zero (Tm.sel (Syn.var 0) Tm.one Tm.zero)

@[simp] theorem Tm.subst_npar (σ : Fin n → Tm m) (y : Tm n) :
    Syn.subst σ (Tm.npar y) = Tm.npar (Syn.subst σ y) := by
  simp only [Tm.npar, Tm.subst_iter, Tm.subst_sel, Tm.subst_zero, Tm.subst_one, Syn.subst_var,
    Syn.up_zero]

namespace NFm

/-- Falsity. -/
def bot : NFm n := eq zero one

/-- Implication. -/
def imp (A B : NFm n) : NFm n := Q (sel (Syn.var 0) A.shift B.shift)

/-- Conjunction. -/
def and (A B : NFm n) : NFm n :=
  Q (gate (Syn.var 0) (sel (Tm.npar (Syn.var 0)) A.shift B.shift))

/-- Existential quantification. -/
def ex (A : NFm (n + 1)) : NFm n := D (gate (Syn.var 0) A.shift)

/-- Disjunction. -/
def or (A B : NFm n) : NFm n := ex (sel (Syn.var 0) A.shift B.shift)

/-- Universal quantification. -/
def all (A : NFm (n + 1)) : NFm n := and (A.subst (inst zero)) (Q A)

theorem imp_subst (A B : NFm n) (σ : Fin n → Tm m) :
    (imp A B).subst σ = imp (A.subst σ) (B.subst σ) := by
  simp only [NFm.imp, subst_Q, sel_subst, Syn.subst_var, Syn.up_zero, shift_subst_up]

theorem and_subst (A B : NFm n) (σ : Fin n → Tm m) :
    (and A B).subst σ = and (A.subst σ) (B.subst σ) := by
  simp only [NFm.and, subst_Q, gate_subst, sel_subst, Tm.subst_npar, Syn.subst_var,
    Syn.up_zero, shift_subst_up]

theorem ex_subst (A : NFm (n + 1)) (σ : Fin n → Tm m) :
    (ex A).subst σ = ex (A.subst (up σ)) := by
  simp only [NFm.ex, subst_D, gate_subst, Syn.subst_var, Syn.up_zero, shift_subst_up]

theorem or_subst (A B : NFm n) (σ : Fin n → Tm m) :
    (or A B).subst σ = or (A.subst σ) (B.subst σ) := by
  simp only [NFm.or, ex_subst, sel_subst, Syn.subst_var, Syn.up_zero, shift_subst_up]

theorem all_subst (A : NFm (n + 1)) (σ : Fin n → Tm m) :
    (all A).subst σ = all (A.subst (up σ)) := by
  simp only [NFm.all, and_subst, subst_Q, subst_inst, Tm.subst_zero]

theorem map_shift_inst (Γ : List (NFm n)) (t : Tm n) :
    (Γ.map NFm.shift).map (fun B => B.subst (inst t)) = Γ := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih => simp only [List.map_cons, ih, subst_inst_shift]

end NFm

namespace NPrf

variable {Γ : List (NFm n)}

theorem wkUnder {A B C : NFm n} (h : NPrf (A :: Γ) C) : NPrf (A :: B :: Γ) C :=
  h.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))

/-- The selector respects equality of its first argument. -/
theorem selCongr {c c' : Tm n} (a b : Tm n) (h : NPrf Γ (.eq c c')) :
    NPrf Γ (.eq (Tm.sel c a b) (Tm.sel c' a b)) := by
  have e := eqCongr (Tm.sel (Syn.var 0) (Syn.shift a) (Syn.shift b)) h
  simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at e
  exact e

/-! ### Falsity -/

/-- From `0 = 1` every equation follows. -/
theorem botEq (h : NPrf Γ NFm.bot) (s t : Tm n) : NPrf Γ (.eq s t) :=
  eqTrans (eqTrans (eqSymm (selZero s t)) (selCongr s t h)) (selSucc zero s t)

theorem botSubst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) {Γ : List (NFm m)},
    NPrf Γ NFm.bot → NPrf Γ (A.subst σ) := by
  induction A with intro m σ Γ h
  | eq s t => exact botEq h _ _
  | Q B ih =>
    have key : ∀ {Δ : List (NFm (m + 1))}, NPrf Δ NFm.bot →
        NPrf Δ ((B.subst (up σ)).subst (repl (succ (Syn.var 0)))) := by
      intro Δ hΔ
      rw [NFm.subst_subst]
      exact ih _ hΔ
    exact qI _ (key h.shift.wk)
  | D B ih =>
    have key : ∀ {Δ : List (NFm (m + 1))}, NPrf Δ NFm.bot →
        NPrf Δ (((B.subst (up (up σ))).subst (up (inst zero))).subst
          (repl (succ (Syn.var 0)))) := by
      intro Δ hΔ
      rw [NFm.subst_subst, NFm.subst_subst]
      exact ih _ hΔ
    exact .dICase _ zero (key h.shift.wk)

/-- Ex falso quodlibet. -/
theorem botE (A : NFm n) (h : NPrf Γ NFm.bot) : NPrf Γ A := by
  have h' := botSubst A Syn.var h
  rwa [NFm.subst_id] at h'

/-! ### Implication -/

theorem impI {A B : NFm n} (h : NPrf (A :: Γ) B) : NPrf Γ (NFm.imp A B) := by
  have h' : NPrf (A.shift :: Γ.map NFm.shift) B.shift := h.shift
  refine qI _ ?_
  rw [NFm.sel_shift_repl, NFm.sel_shift_inst]
  exact (NEquiv.sel_succ _ _ _).mpr
    (cut1 ((NEquiv.sel_zero A B).shift.mp hyp0) (wkUnder h'))

theorem impE {A B : NFm n} (h₁ : NPrf Γ (NFm.imp A B)) (h₂ : NPrf Γ A) : NPrf Γ B := by
  have h := NPrf.qE (succ zero) h₁
    (by rw [NFm.sel_shift_inst]; exact (NEquiv.sel_zero A B).mpr h₂)
  rw [NFm.sel_shift_inst] at h
  exact (NEquiv.sel_succ A zero B).mp h

/-! ### The selector between two formulas -/

/-- Transport of a selector along an equation of its index. -/
theorem selTr {v w : Tm n} (A B : NFm n) (e : NPrf Γ (.eq v w))
    (h : NPrf Γ (NFm.sel v A B)) : NPrf Γ (NFm.sel w A B) :=
  tr' (NFm.sel (Syn.var 0) A.shift B.shift) e (NFm.sel_shift_inst A B v)
    (NFm.sel_shift_inst A B w) h

/-- Both formulas give the selector at any index. -/
theorem selI (w : Tm n) {A B : NFm n} (hA : NPrf Γ A) (hB : NPrf Γ B) :
    NPrf Γ (NFm.sel w A B) := by
  have h := cases (NFm.sel (Syn.var 0) A.shift B.shift) w
    (by rw [NFm.sel_shift_inst]; exact (NEquiv.sel_zero A B).mpr hA)
    (by rw [NFm.sel_shift_repl]; exact (NEquiv.sel_succ _ _ _).mpr hB.shift.wk)
  rwa [NFm.sel_shift_inst] at h

/-- Case analysis on a selector at any index. -/
theorem selE (w : Tm n) {A B C : NFm n} (h : NPrf Γ (NFm.sel w A B))
    (h₁ : NPrf (A :: Γ) C) (h₂ : NPrf (B :: Γ) C) : NPrf Γ C := by
  have h₂' : NPrf (B.shift :: Γ.map NFm.shift) C.shift := h₂.shift
  have hc := cases (NFm.imp (NFm.sel (Syn.var 0) A.shift B.shift) C.shift) w
    (by
      rw [NFm.imp_subst, NFm.sel_shift_inst, NFm.subst_inst_shift]
      exact impI (cut1 ((NEquiv.sel_zero A B).mp hyp0) (wkUnder h₁)))
    (by
      simp only [NFm.imp_subst, NFm.sel_shift_repl, NFm.subst_repl_shift]
      exact impI (cut1 ((NEquiv.sel_succ _ _ _).mp hyp0) (wkUnder (wkUnder h₂'))))
  rw [NFm.imp_subst, NFm.sel_shift_inst, NFm.subst_inst_shift] at hc
  exact impE hc h

/-! ### Conjunction -/

theorem parZero : NPrf Γ (.eq (Tm.npar zero) zero) := .iterZero _ _

theorem parSucc (c : Tm n) : NPrf Γ (.eq (Tm.npar (succ c)) (Tm.sel (Tm.npar c) one zero)) := by
  have h := NPrf.iterSucc (Γ := Γ) c zero (Tm.sel (Syn.var 0) one zero)
  simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_one, Tm.subst_zero] at h
  exact h

theorem parOne : NPrf Γ (.eq (Tm.npar (succ zero)) (succ zero)) :=
  eqTrans (parSucc zero) (eqTrans (selCongr one zero parZero) (selZero one zero))

theorem parTwo : NPrf Γ (.eq (Tm.npar (succ (succ zero))) zero) :=
  eqTrans (parSucc (succ zero)) (eqTrans (selCongr one zero parOne) (selSucc zero one zero))

theorem andI {A B : NFm n} (hA : NPrf Γ A) (hB : NPrf Γ B) : NPrf Γ (NFm.and A B) := by
  have key : ∀ {Δ : List (NFm (n + 1))}, NPrf Δ A.shift → NPrf Δ B.shift →
      NPrf Δ ((NFm.gate (Syn.var 0) (NFm.sel (Tm.npar (Syn.var 0)) A.shift B.shift)).subst
        (repl (succ (Syn.var 0)))) := by
    intro Δ h₁ h₂
    simp only [NFm.gate_subst, NFm.sel_subst, Syn.subst_var, Syn.repl_zero,
      NFm.subst_repl_shift]
    exact (NEquiv.gate_succ _ _).mpr (selI _ h₁ h₂)
  exact qI _ (key hA.shift.wk hB.shift.wk)

/-- The instance of a conjunction at a successor. -/
theorem andInst {A B : NFm n} (h : NPrf Γ (NFm.and A B)) (c : Tm n) :
    NPrf Γ (NFm.sel (Tm.npar (succ c)) A B) := by
  have h' := NPrf.qE (succ c) h
    (by simp only [NFm.gate_subst, Syn.subst_var, Syn.inst_zero]; exact NEquiv.gateZero _)
  simp only [NFm.gate_subst, NFm.sel_subst, Tm.subst_npar, Syn.subst_var, Syn.inst_zero,
    NFm.subst_inst_shift] at h'
  exact (NEquiv.gate_succ _ _).mp h'

theorem andE₁ {A B : NFm n} (h : NPrf Γ (NFm.and A B)) : NPrf Γ A :=
  (NEquiv.sel_zero A B).mp (selTr A B parTwo (andInst h (succ zero)))

theorem andE₂ {A B : NFm n} (h : NPrf Γ (NFm.and A B)) : NPrf Γ B :=
  (NEquiv.sel_succ A zero B).mp (selTr A B parOne (andInst h zero))

/-! ### Existential quantification -/

theorem exI {A : NFm (n + 1)} (t : Tm n) (h : NPrf Γ (A.subst (inst t))) :
    NPrf Γ (NFm.ex A) := by
  have key : ∀ {Δ : List (NFm (n + 1))}, NPrf Δ (A.subst (inst t)).shift →
      NPrf Δ (((NFm.gate (Syn.var 0) A.shift).subst (up (inst t))).subst
        (repl (succ (Syn.var 0)))) := by
    intro Δ h'
    rw [NFm.gate_subst, Syn.subst_var, Syn.up_zero, NFm.shift_subst_up, NFm.gate_shift_repl]
    exact (NEquiv.gate_succ _ _).mpr h'
  exact .dICase _ t (key h.shift.wk)

theorem exE {A : NFm (n + 1)} {C : NFm n} (h₁ : NPrf Γ (NFm.ex A))
    (h₂ : NPrf (A :: Γ.map NFm.shift) C.shift) : NPrf Γ C := by
  refine .dE h₁ ?_
  exact cut1 ((NEquiv.qGate A).mp hyp0) (wkUnder h₂)

/-! ### Disjunction -/

theorem orI₁ {A B : NFm n} (h : NPrf Γ A) : NPrf Γ (NFm.or A B) :=
  exI zero (by rw [NFm.sel_shift_inst]; exact (NEquiv.sel_zero A B).mpr h)

theorem orI₂ {A B : NFm n} (h : NPrf Γ B) : NPrf Γ (NFm.or A B) :=
  exI (succ zero) (by rw [NFm.sel_shift_inst]; exact (NEquiv.sel_succ A zero B).mpr h)

theorem orE {A B C : NFm n} (h : NPrf Γ (NFm.or A B)) (h₁ : NPrf (A :: Γ) C)
    (h₂ : NPrf (B :: Γ) C) : NPrf Γ C := by
  have h₁' : NPrf (A.shift :: Γ.map NFm.shift) C.shift := h₁.shift
  have h₂' : NPrf (B.shift :: Γ.map NFm.shift) C.shift := h₂.shift
  refine exE h ?_
  exact selE (Syn.var 0) hyp0 (wkUnder h₁') (wkUnder h₂')

/-! ### Universal quantification -/

theorem allI {A : NFm (n + 1)} (h : NPrf (Γ.map NFm.shift) A) : NPrf Γ (NFm.all A) := by
  have h0 := h.subst (inst zero)
  rw [NFm.map_shift_inst] at h0
  have hS := h.subst (repl (succ (Syn.var 0)))
  rw [NFm.map_shift_subst_repl] at hS
  exact andI h0 (qI A hS.wk)

theorem allE {A : NFm (n + 1)} (t : Tm n) (h : NPrf Γ (NFm.all A)) :
    NPrf Γ (A.subst (inst t)) :=
  .qE t (andE₂ h) (andE₁ h)

end NPrf

end LeanProofs.ConciseIPRA
