import ConciseIPRA.NativeNamedWitness
import ConciseIPRA.EqPred

/-!
# The literal `0` and variables are enough as witnesses

`dwprf_iff_nprf : DWPrf true true Γ A ↔ NPrf Γ A`: the kernel in which the
introduction of `D` by cases takes the literal `0` or a variable as its
witness, and no other term, derives exactly what the kernel derives.  This
settles further question 2 of the README, as proposed in writing by the
packages `newest_parameter`, `no_witness`, `parameter_witness` and
`uniform_raw`.  Each shape alone is incomplete (`NativeWitnessShape`).

By `dwprf_complete_iff_names` it is enough to derive a name
`D_{x,y} (sel(y, a, x) = a)` for every term `a` (`DWPrf.names`).

* A term that is provably equal to an admissible witness has a name
  (`DWPrf.nameOf`).
* Let `P` be the predecessor term of `T_eq`.  The formula `F(y)`, the name
  of `P(y)`, holds at `0`, with the witness `0` and `P(0) = 0`, and at `S z`
  for a fresh `z`, with the witness `z` and `z = P(S z)`.  So `Q_y F(y)` is
  derivable, by the introduction of `Q` by cases with the dummy witness `0`,
  and `F(S a)` follows by `QE`: a name of `P(S a)`.
* Opening that name at a fresh `b` gives `b = P(S a) = a`, and `b` is an
  admissible witness for the name of `a`.

The two equations `P(0) = 0` and `P(S t) = t` come from the equational
calculus (`EqPred`), which embeds in every `DWPrf z v` (`EqPrf.toDW`): its
induction rule is `QI` by progress followed by `QE`, and it has no rule that
names a witness.  That is the point of the packages' audit of the
predecessor: its derivation needs no coverage and no case split on a formula.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

theorem Tm.IsWit.rn {z v : Bool} {t : Tm n} (h : t.IsWit z v) (ξ : Fin n → Fin m) :
    (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t).IsWit z v := by
  cases t with
  | var i => exact h
  | zero => exact h
  | succ t => exact h.elim
  | iter c a g => exact h.elim

/-- The successor instance of the alias matrix at an arbitrary witness. -/
theorem NFm.aliasM_step' (a w : Tm n) :
    ((NFm.aliasM a).subst (up (inst w))).subst (repl (succ (Syn.var 0)))
      = .eq (Tm.sel (succ (Syn.var 0)) (Syn.shift a) (Syn.shift w)) (Syn.shift a) := by
  simp [NFm.aliasM, Syn.subst_up_shift]

/-- The name of the predecessor of the variable `0`. -/
def NFm.nameP : NFm (n + 1) := .D (NFm.aliasM (Tm.pred (Syn.var 0)))

theorem NFm.nameP_subst (σ : Fin (n + 1) → Tm m) :
    (NFm.nameP : NFm (n + 1)).subst σ = .D (NFm.aliasM (Tm.pred (σ 0))) := by
  simp only [NFm.nameP, NFm.subst_D, NFm.aliasM_subst, Tm.subst_pred, Syn.subst_var]

namespace DWPrf

variable {z v : Bool} {Γ Δ : List (NFm n)} {A : NFm n}

theorem hyp0 : DWPrf z v (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : DWPrf z v Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → DWPrf z v Δ A := by
  induction h with intro Δ s
  | hyp h => exact .hyp (s h)
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t hw _ ih =>
    exact .dICase B t hw (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : DWPrf z v Γ A) : DWPrf z v (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : DWPrf z v Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    DWPrf z v (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero _ _
  | iterSucc c a h =>
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ) h₂
  | dE _ _ ih₁ ih₂ =>
    have h := ih₂ (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ) h
  | dICase B t hw _ ih =>
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ (hw.rn ξ) h
  | qIInd s₁ s₂ _ ih =>
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd _ _ h

theorem shift (h : DWPrf z v Γ A) : DWPrf z v (Γ.map NFm.shift) A.shift := h.ren Fin.succ

/-! ### Equality -/

theorem eqRefl (t : Tm n) : DWPrf z v Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : DWPrf z v Γ (.eq s t)) : DWPrf z v Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : DWPrf z v Γ (.eq s t)) (h₂ : DWPrf z v Γ (.eq t u)) :
    DWPrf z v Γ (.eq s u) :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

theorem selSucc (c a b : Tm n) : DWPrf z v Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := DWPrf.iterSucc (z := z) (v := v) (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

end DWPrf

/-! ### The equational calculus inside -/

theorem ECtx.map_eq_shift (Γ : ECtx n) :
    (Γ.shift).map (fun p => NFm.eq p.1 p.2) = (Γ.map fun p => NFm.eq p.1 p.2).map NFm.shift := by
  rw [ECtx.shift, ECtx.subst, List.map_map, List.map_map]
  exact List.map_congr_left fun p _ => rfl

/-- **The equational calculus embeds in the kernel with any restriction of the
witness**: its induction rule is `QI` by progress followed by `QE`. -/
theorem EqPrf.toDW {z v : Bool} {Γ : ECtx n} {s t : Tm n} (h : EqPrf Γ s t) :
    DWPrf z v (Γ.map fun p => NFm.eq p.1 p.2) (.eq s t) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem (f := fun p : Tm _ × Tm _ => NFm.eq p.1 p.2) h)
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | ind s t a _ _ ih₀ ihS =>
    rw [List.map_cons, ECtx.map_eq_shift] at ihS
    exact .qE a (.qIInd s t ihS) ih₀

namespace DWPrf

variable {z v : Bool} {Γ : List (NFm n)} {A : NFm n}

/-- An equation of the equational calculus, in any context. -/
theorem ofEq {s t : Tm n} (h : EqPrf [] s t) : DWPrf z v Γ (.eq s t) :=
  h.toDW.weaken (List.nil_subset _)

/-- A term that is provably equal to an admissible witness has a name. -/
theorem nameOf {b w : Tm n} (hw : w.IsWit z v) (h : DWPrf z v Γ (.eq w b)) :
    DWPrf z v Γ (.D (NFm.aliasM b)) := by
  refine .dICase _ w hw ?_
  rw [NFm.aliasM_step']
  exact eqTrans (selSucc _ _ _) h.shift.wk

/-- Introduction of `Q` by cases, with the dummy witness `0`. -/
theorem qI (B : NFm (n + 1))
    (h : DWPrf true v ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : DWPrf true v Γ (.Q B) := by
  have hD : DWPrf true v Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dICase _ zero rfl ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show DWPrf true v (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- The names of the predecessors, for all numbers at once. -/
theorem namePQ : DWPrf true true Γ (.Q NFm.nameP) := by
  refine qI _ ?_
  rw [NFm.nameP_subst, NFm.nameP_subst, Syn.repl_zero]
  exact nameOf (w := Syn.var 0) rfl (eqSymm (ofEq (EqPrf.pred_succ _)))

/-- **Every term has a name**, with `0` and variables as the only
witnesses. -/
theorem names (a : Tm n) : DWPrf true true Γ (.D (NFm.aliasM a)) := by
  -- the name of `P(S a)`
  have h0 : DWPrf true true Γ ((NFm.nameP : NFm (n + 1)).subst (inst zero)) := by
    rw [NFm.nameP_subst, Syn.inst_zero]
    exact nameOf (w := zero) rfl (eqSymm (ofEq EqPrf.pred_zero))
  have hT := DWPrf.qE (succ a) namePQ h0
  rw [NFm.nameP_subst, Syn.inst_zero] at hT
  -- opened at a fresh `b`, it gives `b = P(S a) = a`
  refine .dE hT ?_
  rw [NFm.shift, NFm.subst_D, NFm.aliasM_subst]
  have k : DWPrf true true (.Q (NFm.aliasM (Tm.pred (succ a))) :: Γ.map NFm.shift)
      ((NFm.aliasM (Tm.pred (succ a))).subst (inst (succ zero))) := by
    refine .qE (succ zero) hyp0 ?_
    rw [NFm.aliasM_inst]
    exact .iterZero _ _
  rw [NFm.aliasM_inst] at k
  have e : DWPrf true true (.Q (NFm.aliasM (Tm.pred (succ a))) :: Γ.map NFm.shift)
      (.eq (Syn.shift (Tm.pred (succ a))) (Syn.shift a)) := by
    rw [Syn.shift, Syn.shift, Tm.subst_pred, Tm.subst_succ]
    exact ofEq (EqPrf.pred_succ _)
  exact nameOf (w := Syn.var 0) rfl (eqTrans (.trOne (Syn.var 0) k (selSucc zero _ _)) e)

end DWPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The literal `0` and variables are enough as witnesses of `DI`.** -/
theorem dwprf_iff_nprf : DWPrf true true Γ A ↔ NPrf Γ A :=
  (dwprf_complete_iff_names true).2 (fun _ a => DWPrf.names a) Γ A

end LeanProofs.ConciseIPRA
