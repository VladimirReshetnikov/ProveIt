import ConciseIPRA.NativeEq

/-!
# The inherited calculus and the kernel are the same consequence relation

The research reports state the native scalar core with two stronger rules than
the kernel `NPrf` of `Native`:

* **Tr** transports along an equation in an *arbitrary* formula template,
  including templates with `Q` and `D`;
* **DI by progress** introduces `D_{x,y} E(x, y)` with a witness for `x`.

`IPrf` is that inherited calculus, rule for rule.  The kernel replaces them by

* `trEq`: transport inside an equation only;
* `qIInd`: from `E(z) ⊢ E(S z)` infer `Q_y E(y)`, with no witness.

`iprf_iff_nprf` proves that the two calculi derive the same sequents, for
every context.  Each kernel rule is an instance of an inherited rule or a
three-step derivation in the inherited calculus (`NPrf.toIPrf`); conversely the
two inherited rules are the derived rules `NPrf.tr` and `NPrf.dIProg`
(`IPrf.toNPrf`).  So every result about `NPrf`, in particular the
bi-interpretation with iPRA, is a result about the calculus of the reports.

The progress rule in the form `qIInd` is the proposal of the packages
`Research/direct_closure` and `Research/direct_closure_qprogress`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

/-- Derivability in the native scalar core as stated in the research reports. -/
inductive IPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : IPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      IPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      IPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Tr: transport along an equation in any formula template. -/
  | tr {n : ℕ} {Γ : List (NFm n)} (H : NFm (n + 1)) {s t : Tm n}
      (h₁ : IPrf Γ (.eq s t)) (h₂ : IPrf Γ (H.subst (inst s))) : IPrf Γ (H.subst (inst t))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : IPrf Γ (.Q B)) (h₂ : IPrf Γ (B.subst (inst zero))) : IPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : IPrf Γ (.D B)) (h₂ : IPrf (.Q B :: Γ.map NFm.shift) A.shift) : IPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : IPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      IPrf Γ (.D B)
  /-- DI by progress: from `E(t, z) ⊢ E(t, S z)` with `z` fresh infer
  `D_{x,y} E`, for a literal equation `E` only. -/
  | dIProg {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 2)) (t : Tm n)
      (h : IPrf ((NFm.eq s₁ s₂).subst (up (inst t)) :: Γ.map NFm.shift)
        (((NFm.eq s₁ s₂).subst (up (inst t))).subst (repl (succ (var 0))))) :
      IPrf Γ (.D (.eq s₁ s₂))

variable {n : ℕ} {Γ : List (NFm n)} {A : NFm n}

/-- DI by progress, the witnessed form of the research reports: from
`E(t, z) ⊢ E(t, S z)` with `z` fresh infer `D_{x,y} E`, for a literal equation
`E`.  Derived from `qIInd`, `qE` and `dICase`. -/
theorem NPrf.dIProg (s₁ s₂ : Tm (n + 2)) (t : Tm n)
    (h : NPrf ((NFm.eq s₁ s₂).subst (up (inst t)) :: Γ.map NFm.shift)
      (((NFm.eq s₁ s₂).subst (up (inst t))).subst (repl (succ (var 0))))) :
    NPrf Γ (.D (.eq s₁ s₂)) := by
  have hQ : NPrf Γ (.Q ((NFm.eq s₁ s₂).subst (up (inst t)))) := .qIInd _ _ h
  refine .dICase (.eq s₁ s₂) t ?_
  have hQ' : NPrf ((((NFm.eq s₁ s₂).subst (up (inst t))).subst (inst zero)).shift
        :: Γ.map NFm.shift)
      (.Q (((NFm.eq s₁ s₂).subst (up (inst t))).subst (up (fun i => Syn.var i.succ)))) :=
    hQ.shift.wk
  have h0 : NPrf ((((NFm.eq s₁ s₂).subst (up (inst t))).subst (inst zero)).shift
        :: Γ.map NFm.shift)
      ((((NFm.eq s₁ s₂).subst (up (inst t))).subst (up (fun i => Syn.var i.succ))).subst
        (inst zero)) := by
    rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero]
    exact NPrf.hyp0
  have h' := NPrf.qE (succ (var 0)) hQ' h0
  rwa [NFm.subst_dummy_up_inst] at h'

/-- Every inherited rule is a derived rule of the kernel. -/
theorem IPrf.toNPrf (h : IPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | tr H _ _ ih₁ ih₂ => exact .tr H ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | dIProg s₁ s₂ t _ ih => exact .dIProg s₁ s₂ t ih

/-- Every kernel rule is a derived rule of the inherited calculus: `trEq` is an
instance of `tr`, and `qIInd` is `dIProg` at a dummy witness followed by
`dE`. -/
theorem NPrf.toIPrf (h : NPrf Γ A) : IPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ ih₁ ih₂ => exact .tr (.eq a b) ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | @qIInd _ Γ s t _ ih =>
    have hD : IPrf Γ (.D ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))) := by
      refine .dIProg _ _ zero ?_
      rw [show (NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
          (Syn.subst (up (fun i => Syn.var i.succ)) t)).subst (up (inst zero)) = .eq s t from
        NFm.subst_dummy_inst (.eq s t) zero]
      exact ih
    exact .dE hD (.hyp List.mem_cons_self)

/-- **The inherited calculus and the kernel derive the same sequents.** -/
theorem iprf_iff_nprf : IPrf Γ A ↔ NPrf Γ A := ⟨IPrf.toNPrf, NPrf.toIPrf⟩

end LeanProofs.ConciseIPRA
