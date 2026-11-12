import ConciseIPRA.NativeStruct
import ConciseIPRA.TeqArith

/-!
# Equality and interderivability in the native scalar core

The only equality rule of the native calculus is the equational transport
rule `trEq`.  This module derives from it

* reflexivity, symmetry, transitivity and congruence of equations;
* the simultaneous Leibniz rule for equations, `NPrf.leibnizEq`;
* equation induction `NPrf.eqInd`, from the progress rule `qIInd`;
* the two equations of the selector `sel c a b = I(c, a; u. b)`.

It then introduces interderivability over a context, `NEquivIn Γ A B`, and
proves that it is a congruence for the quantifiers `Q` and `D`.  The quantifier
`Q` is contravariant in the instance at zero, so both directions are needed.
By induction on the formula this gives

* the simultaneous Leibniz rule `NPrf.leibniz` for every formula, and so
  transport `NPrf.tr` in an arbitrary formula template, which is the rule of
  the research reports.

`NEquiv A B` is interderivability over the empty context.
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

theorem map_shift_subst_repl (Γ : List (NFm n)) (c : Tm (n + 1)) :
    (Γ.map NFm.shift).map (fun A => A.subst (repl c)) = Γ.map NFm.shift := by
  rw [List.map_map]
  exact List.map_congr_left fun A _ => subst_repl_shift A c

end NFm

namespace NPrf

variable {Γ : List (NFm n)}

/-- The primitive transport rule with the template and its two instances
named. -/
theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : NPrf Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : NPrf Γ A) : NPrf Γ A' := by
  subst hH hA hA'
  exact .trEq a b h₁ h₂

theorem eqRefl (t : Tm n) : NPrf Γ (.eq t t) :=
  trE (.eq (Syn.var 0) (Syn.shift t)) rfl (.iterZero t (Syn.var 0)) (by simp) (by simp)
    (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : NPrf Γ (.eq s t)) : NPrf Γ (.eq t s) :=
  trE (.eq (Syn.var 0) (Syn.shift s)) rfl h (by simp) (by simp) (eqRefl s)

theorem eqTrans {s t u : Tm n} (h₁ : NPrf Γ (.eq s t)) (h₂ : NPrf Γ (.eq t u)) :
    NPrf Γ (.eq s u) :=
  trE (.eq (Syn.shift s) (Syn.var 0)) rfl h₂ (by simp) (by simp) h₁

/-- Replacement of equals inside a term. -/
theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : NPrf Γ (.eq s t)) :
    NPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  trE (A := .eq (Syn.subst (inst s) h) (Syn.subst (inst s) h))
    (.eq (Syn.shift (Syn.subst (inst s) h)) h) rfl e (by simp) (by simp) (eqRefl _)

/-- The simultaneous Leibniz rule for an equation. -/
theorem leibnizEq (a b : Tm k) (σ σ' : Fin k → Tm n) (he : ∀ i, NPrf Γ (.eq (σ i) (σ' i)))
    (h : NPrf Γ ((NFm.eq a b).subst σ)) : NPrf Γ ((NFm.eq a b).subst σ') := by
  have key : ∀ j, j ≤ k →
      NPrf Γ ((NFm.eq a b).subst fun i => if i.val < j then σ' i else σ i) := by
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

/-- Introduction of `Q` for an equation by progress: from `E(z) ⊢ E(S z)` with
`z` fresh, infer `Q_y E(y)`.  This is the primitive rule. -/
theorem qIProg (s t : Tm (n + 1))
    (h : NPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) : NPrf Γ (.Q (.eq s t)) :=
  .qIInd s t h

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

/-- Interderivability of two formulas over a context. -/
def NEquivIn (Γ : List (NFm n)) (A B : NFm n) : Prop := NPrf (A :: Γ) B ∧ NPrf (B :: Γ) A

namespace NEquivIn

variable {Γ : List (NFm n)} {A B : NFm n}

theorem symm (e : NEquivIn Γ A B) : NEquivIn Γ B A := ⟨e.2, e.1⟩

theorem mp (e : NEquivIn Γ A B) {Δ : List (NFm n)} (hΔ : Γ ⊆ Δ) (h : NPrf Δ A) : NPrf Δ B :=
  .cut1 h (e.1.weaken (List.cons_subset_cons _ hΔ))

theorem mpr (e : NEquivIn Γ A B) {Δ : List (NFm n)} (hΔ : Γ ⊆ Δ) (h : NPrf Δ B) : NPrf Δ A :=
  e.symm.mp hΔ h

/-- Replacement of the bound variable, over a context that does not mention
it. -/
theorem substRepl {B B' : NFm (n + 1)} (e : NEquivIn (Γ.map NFm.shift) B B') (c : Tm (n + 1)) :
    NEquivIn (Γ.map NFm.shift) (B.subst (repl c)) (B'.subst (repl c)) := by
  have h₁ := e.1.subst (repl c)
  have h₂ := e.2.subst (repl c)
  rw [List.map_cons, NFm.map_shift_subst_repl] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The step shared by the congruence rules for `Q` and `D`. -/
theorem qStep {B B' : NFm (n + 1)} (e : NEquivIn (Γ.map NFm.shift) B B')
    {Δ : List (NFm (n + 1))} (hΔ : Γ.map NFm.shift ⊆ Δ) :
    NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B'.subst (repl (succ (Syn.var 0)))) := by
  have hΔ' : ∀ X Y : NFm (n + 1), Γ.map NFm.shift ⊆ X :: Y :: Δ := fun _ _ _ hA =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hΔ hA))
  have h0 : NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B.subst (repl zero)) := by
    rw [NFm.shift_subst_inst_zero]
    exact (e.substRepl zero).mpr (hΔ' _ _) NPrf.hyp0
  have hQ : NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (.Q (B.subst (up (fun i => Syn.var i.succ)))) :=
    .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [← NFm.subst_dummy_up_inst] at h0
  have h := NPrf.qE (succ (Syn.var 0)) hQ h0
  rw [NFm.subst_dummy_up_inst] at h
  exact (e.substRepl _).mp (hΔ' _ _) h

/-- `Q` respects interderivability of its matrix. -/
protected theorem Q {B B' : NFm (n + 1)} (e : NEquivIn (Γ.map NFm.shift) B B') :
    NEquivIn Γ (.Q B) (.Q B') :=
  ⟨.qI _ (qStep e (List.Subset.refl _)), .qI _ (qStep e.symm (List.Subset.refl _))⟩

theorem dStep {B B' : NFm (n + 2)} (e : NEquivIn ((Γ.map NFm.shift).map NFm.shift) B B') :
    NPrf (.D B :: Γ) (.D B') := by
  refine .dE NPrf.hyp0 ?_
  show NPrf _ (.D (B'.subst (up (up (fun i => Syn.var i.succ)))))
  refine .dICase _ (Syn.var 0) ?_
  rw [NFm.subst_upup_inst_var]
  exact qStep e (List.map_subset _ (List.map_subset _ (List.subset_cons_self _ _)))

/-- `D` respects interderivability of its matrix. -/
protected theorem D {B B' : NFm (n + 2)} (e : NEquivIn ((Γ.map NFm.shift).map NFm.shift) B B') :
    NEquivIn Γ (.D B) (.D B') :=
  ⟨dStep e, dStep e.symm⟩

end NEquivIn

namespace NPrf

variable {Γ : List (NFm n)}

/-- Equal substitutions stay equal under a binder. -/
theorem upEq {σ σ' : Fin k → Tm n} (he : ∀ i, NPrf Γ (.eq (σ i) (σ' i))) :
    ∀ i, NPrf (Γ.map NFm.shift) (.eq (up σ i) (up σ' i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact eqRefl _
  · rw [up_succ, up_succ]
    exact (he j).shift

/-- Substitutions that are provably equal give interderivable instances. -/
theorem leibnizIn (A : NFm k) : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin k → Tm n),
    (∀ i, NPrf Γ (.eq (σ i) (σ' i))) → NEquivIn Γ (A.subst σ) (A.subst σ') := by
  induction A with
  | eq a b =>
    intro n Γ σ σ' he
    exact ⟨leibnizEq a b σ σ' (fun i => (he i).wk) hyp0,
      leibnizEq a b σ' σ (fun i => eqSymm (he i).wk) hyp0⟩
  | Q B ih => intro n Γ σ σ' he; exact .Q (ih _ _ (upEq he))
  | D B ih => intro n Γ σ σ' he; exact .D (ih _ _ (upEq (upEq he)))

/-- The simultaneous Leibniz rule. -/
theorem leibniz (A : NFm k) (σ σ' : Fin k → Tm n) (he : ∀ i, NPrf Γ (.eq (σ i) (σ' i)))
    (h : NPrf Γ (A.subst σ)) : NPrf Γ (A.subst σ') :=
  (leibnizIn A σ σ' he).mp (List.Subset.refl _) h

/-- Tr in an arbitrary formula template: the transport rule of the research
reports, derived from its equational case by induction on the template. -/
theorem tr (H : NFm (n + 1)) {s t : Tm n} (h₁ : NPrf Γ (.eq s t))
    (h₂ : NPrf Γ (H.subst (inst s))) : NPrf Γ (H.subst (inst t)) :=
  leibniz H (inst s) (inst t) (fun i => Fin.cases h₁ (fun j => by
    rw [inst_succ, inst_succ]; exact eqRefl _) i) h₂

/-- The transport rule with the two instances of the template named. -/
theorem tr' (H : NFm (n + 1)) {s t : Tm n} {A A' : NFm n} (h₁ : NPrf Γ (.eq s t))
    (hA : H.subst (inst s) = A) (hA' : H.subst (inst t) = A') (h₂ : NPrf Γ A) :
    NPrf Γ A' := by
  subst hA hA'
  exact tr H h₁ h₂

end NPrf

/-- Interderivability of two formulas of the native calculus. -/
def NEquiv (A B : NFm n) : Prop := NEquivIn [] A B

namespace NEquiv

variable {A B C : NFm n} {Γ : List (NFm n)}

theorem refl (A : NFm n) : NEquiv A A := ⟨NPrf.hyp0, NPrf.hyp0⟩

theorem symm (e : NEquiv A B) : NEquiv B A := ⟨e.2, e.1⟩

theorem mp (e : NEquiv A B) (h : NPrf Γ A) : NPrf Γ B := NEquivIn.mp e (List.nil_subset _) h

theorem mpr (e : NEquiv A B) (h : NPrf Γ B) : NPrf Γ A := e.symm.mp h

theorem trans (e₁ : NEquiv A B) (e₂ : NEquiv B C) : NEquiv A C :=
  ⟨e₂.mp e₁.1, e₁.mpr e₂.2⟩

theorem subst (e : NEquiv A B) (σ : Fin n → Tm m) : NEquiv (A.subst σ) (B.subst σ) :=
  ⟨e.1.subst σ, e.2.subst σ⟩

theorem shift (e : NEquiv A B) : NEquiv A.shift B.shift := e.subst _

/-- The step shared by the congruence rules for `Q` and `D`. -/
theorem qStep {B B' : NFm (n + 1)} (e : NEquiv B B') {Δ : List (NFm (n + 1))} :
    NPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B'.subst (repl (succ (Syn.var 0)))) :=
  NEquivIn.qStep (Γ := []) e (List.nil_subset _)

/-- `Q` respects interderivability. -/
protected theorem Q {B B' : NFm (n + 1)} (e : NEquiv B B') : NEquiv (.Q B) (.Q B') :=
  NEquivIn.Q (Γ := []) e

/-- `D` respects interderivability. -/
protected theorem D {B B' : NFm (n + 2)} (e : NEquiv B B') : NEquiv (.D B) (.D B') :=
  NEquivIn.D (Γ := []) e

end NEquiv

end LeanProofs.ConciseIPRA
