import ConciseIPRA.NativeStruct
import ConciseIPRA.TeqArith

/-!
# Equality and interderivability in the native scalar core

The only equality rule of the native calculus is the transport rule `tr`.
This module derives from it

* reflexivity, symmetry, transitivity and congruence of equations;
* the simultaneous Leibniz rule `NPrf.leibniz`;
* equation induction `NPrf.eqInd`, from the progress form of `D`-introduction;
* the two equations of the selector `sel c a b = I(c, a; u. b)`.

It also introduces interderivability `NEquiv A B` of two formulas and proves
that it is a congruence for the quantifiers `Q` and `D`.  The quantifier `Q`
is contravariant in the instance at zero, so both directions are needed.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

namespace NFm

/-- Instantiating a variable that was weakened under one binder. -/
theorem subst_dummy_up_inst (B : NFm (n + 1)) (s : Tm (n + 1)) :
    (B.subst (up (fun i => Syn.var i.succ))).subst (inst s) = B.subst (repl s) := by
  rw [subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem shift_subst_inst (B : NFm (n + 1)) (t : Tm n) :
    (B.subst (inst t)).shift = B.subst (repl (Syn.shift t)) := by
  unfold NFm.shift
  rw [subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Syn.shift]

theorem shift_subst_inst_zero (B : NFm (n + 1)) :
    (B.subst (inst zero)).shift = B.subst (repl zero) :=
  shift_subst_inst B zero

/-- Weakening under two binders followed by identification of the new
variable with the outer bound one. -/
theorem subst_upup_inst_var (B : NFm (n + 2)) :
    (B.subst (up (up (fun i => Syn.var i.succ)))).subst (up (inst (Syn.var 0))) = B := by
  rw [subst_subst]
  refine B.subst_eq_self fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [up_succ, Syn.subst_up_shift]
    refine Fin.cases ?_ (fun l => ?_) j <;> simp

/-- Weakening under one binder followed by identification of the new variable
with the bound one. -/
theorem subst_up_inst_var (B : NFm (n + 1)) :
    (B.subst (up (fun i => Syn.var i.succ))).subst (inst (Syn.var 0)) = B := by
  rw [subst_subst]
  refine B.subst_eq_self fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem subst_repl_shift (A : NFm n) (s : Tm (n + 1)) :
    A.shift.subst (repl s) = A.shift := by
  unfold NFm.shift
  rw [subst_subst]
  exact A.subst_ext fun i => by simp

end NFm

namespace NPrf

variable {Γ : List (NFm n)}

/-- The transport rule with the two instances of the template named. -/
theorem tr' (H : NFm (n + 1)) {s t : Tm n} {A A' : NFm n} (h₁ : NPrf Γ (.eq s t))
    (hA : H.subst (inst s) = A) (hA' : H.subst (inst t) = A') (h₂ : NPrf Γ A) :
    NPrf Γ A' := by
  subst hA hA'
  exact .tr H h₁ h₂

theorem eqRefl (t : Tm n) : NPrf Γ (.eq t t) :=
  tr' (.eq (Syn.var 0) (Syn.shift t)) (.iterZero t (Syn.var 0)) (by simp) (by simp)
    (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : NPrf Γ (.eq s t)) : NPrf Γ (.eq t s) :=
  tr' (.eq (Syn.var 0) (Syn.shift s)) h (by simp) (by simp) (eqRefl s)

theorem eqTrans {s t u : Tm n} (h₁ : NPrf Γ (.eq s t)) (h₂ : NPrf Γ (.eq t u)) :
    NPrf Γ (.eq s u) :=
  tr' (.eq (Syn.shift s) (Syn.var 0)) h₂ (by simp) (by simp) h₁

/-- Replacement of equals inside a term. -/
theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : NPrf Γ (.eq s t)) :
    NPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  tr' (A := .eq (Syn.subst (inst s) h) (Syn.subst (inst s) h))
    (.eq (Syn.shift (Syn.subst (inst s) h)) h) e (by simp) (by simp) (eqRefl _)

/-- The simultaneous Leibniz rule. -/
theorem leibniz (A : NFm k) (σ σ' : Fin k → Tm n) (he : ∀ i, NPrf Γ (.eq (σ i) (σ' i)))
    (h : NPrf Γ (A.subst σ)) : NPrf Γ (A.subst σ') := by
  have key : ∀ j, j ≤ k → NPrf Γ (A.subst fun i => if i.val < j then σ' i else σ i) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hj' := ih (Nat.le_of_succ_le hj)
      refine tr' (A.subst fun i => if i.val = j then Syn.var 0
          else Syn.shift (if i.val < j then σ' i else σ i)) (he ⟨j, hj⟩) ?_ ?_ hj'
      · rw [NFm.subst_subst]
        refine A.subst_ext fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · simp [hi]
      · rw [NFm.subst_subst]
        refine A.subst_ext fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · have hlt : i.val < j + 1 ↔ i.val < j := by omega
          simp [hi, hlt]
  have h' := key k le_rfl
  simpa using h'

/-- Introduction of `Q` for an equation by progress: from `E(z) ⊢ E(S z)` with
`z` fresh, infer `Q_y E(y)`. -/
theorem qIProg (s t : Tm (n + 1))
    (h : NPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) : NPrf Γ (.Q (.eq s t)) := by
  have e : (NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
        (Syn.subst (up (fun i => Syn.var i.succ)) t)).subst (up (inst zero)) = .eq s t :=
    NFm.subst_dummy_inst (.eq s t) zero
  have hD : NPrf Γ (.D (.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
      (Syn.subst (up (fun i => Syn.var i.succ)) t))) := by
    refine .dIProg _ _ zero ?_
    rw [e]
    exact h
  refine .dE hD ?_
  show NPrf (.Q (.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
      (Syn.subst (up (fun i => Syn.var i.succ)) t)) :: Γ.map NFm.shift)
    (.Q (.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
      (Syn.subst (up (fun i => Syn.var i.succ)) t)))
  exact hyp0

/-- Equation induction. -/
theorem eqInd (s t : Tm (n + 1)) (u : Tm n) (h0 : NPrf Γ ((NFm.eq s t).subst (inst zero)))
    (hS : NPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    NPrf Γ ((NFm.eq s t).subst (inst u)) :=
  .qE u (qIProg s t hS) h0

theorem selZero (a b : Tm n) : NPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : NPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := NPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rw [Syn.subst_inst_shift] at h
  exact h

end NPrf

/-- Interderivability of two formulas of the native calculus. -/
def NEquiv (A B : NFm n) : Prop := NPrf [A] B ∧ NPrf [B] A

namespace NEquiv

variable {A B C : NFm n} {Γ : List (NFm n)}

theorem refl (A : NFm n) : NEquiv A A := ⟨NPrf.hyp0, NPrf.hyp0⟩

theorem symm (e : NEquiv A B) : NEquiv B A := ⟨e.2, e.1⟩

theorem mp (e : NEquiv A B) (h : NPrf Γ A) : NPrf Γ B := by
  refine e.1.cut fun C hC => ?_
  rw [List.mem_singleton] at hC
  subst hC
  exact h

theorem mpr (e : NEquiv A B) (h : NPrf Γ B) : NPrf Γ A := e.symm.mp h

theorem trans (e₁ : NEquiv A B) (e₂ : NEquiv B C) : NEquiv A C :=
  ⟨e₂.mp e₁.1, e₁.mpr e₂.2⟩

theorem subst (e : NEquiv A B) (σ : Fin n → Tm m) : NEquiv (A.subst σ) (B.subst σ) :=
  ⟨e.1.subst σ, e.2.subst σ⟩

theorem shift (e : NEquiv A B) : NEquiv A.shift B.shift := e.subst _

theorem ofEq (h : A = B) : NEquiv A B := h ▸ refl A

/-- The step shared by the congruence rules for `Q` and `D`. -/
theorem qStep {B B' : NFm (n + 1)} (e : NEquiv B B') {Δ : List (NFm (n + 1))} :
    NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B'.subst (repl (succ (Syn.var 0)))) := by
  have h0 : NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B.subst (repl zero)) := by
    rw [NFm.shift_subst_inst_zero]
    exact (e.subst _).mpr NPrf.hyp0
  have hQ : NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (.Q (B.subst (up (fun i => Syn.var i.succ)))) :=
    .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [← NFm.subst_dummy_up_inst] at h0
  have h := NPrf.qE (succ (Syn.var 0)) hQ h0
  rw [NFm.subst_dummy_up_inst] at h
  exact (e.subst _).mp h

/-- `Q` respects interderivability. -/
protected theorem Q {B B' : NFm (n + 1)} (e : NEquiv B B') : NEquiv (.Q B) (.Q B') :=
  ⟨.qI _ (qStep e), .qI _ (qStep e.symm)⟩

theorem dStep {B B' : NFm (n + 2)} (e : NEquiv B B') : NPrf [.D B] (.D B') := by
  refine .dE NPrf.hyp0 ?_
  show NPrf _ (.D (B'.subst (up (up (fun i => Syn.var i.succ)))))
  refine .dICase _ (Syn.var 0) ?_
  rw [NFm.subst_upup_inst_var]
  exact qStep e

/-- `D` respects interderivability. -/
protected theorem D {B B' : NFm (n + 2)} (e : NEquiv B B') : NEquiv (.D B) (.D B') :=
  ⟨dStep e, dStep e.symm⟩

end NEquiv

end LeanProofs.ConciseIPRA
