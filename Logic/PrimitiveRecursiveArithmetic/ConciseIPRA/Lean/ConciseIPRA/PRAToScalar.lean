import ConciseIPRA.TeqRec
import ConciseIPRA.TeqReflect
import ConciseIPRA.PR
import ConciseIPRA.Interpretation

/-!
# `iPRA` inside `T_eq`

Every primitive recursive function symbol `f : PR k` is compiled to a term
`code f` of `T_eq` in `k` variables: composition is substitution and primitive
recursion is the derived binder `Tm.prc`.  A term of `iPRA` is translated by
substituting the translated arguments into the code of its head symbol.

The translation commutes with substitution syntactically, and every axiom of
`iPRA` becomes a theorem of `T_eq`: the defining equations of projections and
compositions are reflexivity, the recursion equations are those of `Tm.prc`,
and quantifier-free induction is `Teq.qfInd`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m k : ℕ}

namespace FromPRA

/-- The term of `T_eq` computing a primitive recursive function symbol. -/
def code : {k : ℕ} → PR k → Tm k
  | _, .zero => Tm.zero
  | _, .succ => Tm.succ (Syn.var 0)
  | _, .proj i => Syn.var i
  | _, .comp f gs => Syn.subst (fun j => code (gs j)) (code f)
  | _, .prec f g =>
      Tm.prc (Syn.var 0) (shift (code f))
        (Syn.subst (up (up (fun i => Syn.var i.succ))) (code g))

theorem code_proj (i : Fin k) : code (.proj i) = Syn.var i := rfl

theorem code_comp {l : ℕ} (f : PR l) (gs : Fin l → PR k) :
    code (.comp f gs) = Syn.subst (fun j => code (gs j)) (code f) := rfl

theorem code_prec (f : PR k) (g : PR (k + 2)) :
    code (.prec f g)
      = Tm.prc (Syn.var 0) (shift (code f))
          (Syn.subst (up (up (fun i => Syn.var i.succ))) (code g)) := rfl

/-- The translation of the terms of `iPRA` into `T_eq`. -/
def sigma : PTm n → Tm n
  | .var i => Syn.var i
  | .app f ts => Syn.subst (fun i => sigma (ts i)) (code f)

@[simp] theorem sigma_var (i : Fin n) : sigma (Syn.var i : PTm n) = Syn.var i := rfl

theorem sigma_app (f : PR k) (ts : Fin k → PTm n) :
    sigma (PTm.app f ts) = Syn.subst (fun i => sigma (ts i)) (code f) := rfl

@[simp] theorem sigma_zero : sigma (PTm.zero : PTm n) = Tm.zero := rfl

@[simp] theorem sigma_succ (t : PTm n) : sigma (PTm.succ t) = Tm.succ (sigma t) := rfl

theorem sigma_app_var (f : PR k) : sigma (PTm.app f Syn.var) = code f := by
  rw [sigma_app]
  exact Syn.subst_id _

/-- The translation commutes with substitution, syntactically. -/
theorem sigma_subst (ρ : Fin n → PTm m) (t : PTm n) :
    sigma (Syn.subst ρ t) = Syn.subst (fun i => sigma (ρ i)) (sigma t) := by
  induction t with
  | var i => rfl
  | app f ts ih =>
    simp only [PTm.subst_app, sigma_app, Syn.subst_subst, ih]

theorem sigma_inst (t : PTm n) : (fun i => sigma (inst t i)) = inst (sigma t) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem sigma_repl (s : PTm (n + 1)) : (fun i => sigma (repl s i)) = repl (sigma s) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- The term translation from `iPRA` to `T_eq`. -/
def morph : TmMorph PTm TeqAx where
  f _ := sigma
  f_var _ := rfl
  f_subst ρ t := by
    rw [sigma_subst]
    exact Prf.eqRefl _

/-! ### The axioms of `iPRA` hold in `T_eq` under the translation -/

theorem ax_proj (i : Fin k) :
    [] ⊢[TeqAx] sigma (PTm.app (.proj i) Syn.var) ≐ sigma (Syn.var i) := by
  rw [sigma_app_var, code_proj]
  exact Prf.eqRefl _

theorem ax_comp {l : ℕ} (f : PR l) (gs : Fin l → PR k) :
    [] ⊢[TeqAx] sigma (PTm.app (.comp f gs) Syn.var)
      ≐ sigma (PTm.app f (fun j => PTm.app (gs j) Syn.var)) := by
  rw [sigma_app_var, code_comp, sigma_app]
  simp only [sigma_app_var]
  exact Prf.eqRefl _

theorem ax_precZero (f : PR k) (g : PR (k + 2)) :
    [] ⊢[TeqAx] sigma (PTm.app (.prec f g) (inst PTm.zero)) ≐ sigma (PTm.app f Syn.var) := by
  rw [sigma_app_var, sigma_app, sigma_inst, sigma_zero, code_prec, Tm.subst_prc,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
  exact Q.prc_zero _ _

theorem ax_precSucc (f : PR k) (g : PR (k + 2)) :
    [] ⊢[TeqAx] sigma (PTm.app (.prec f g) (repl (PTm.succ (Syn.var 0))))
      ≐ sigma (PTm.app g
          (Fin.cases (Syn.var 0) (repl (PTm.app (.prec f g) Syn.var)))) := by
  have e1 : sigma (PTm.app (.prec f g) (repl (PTm.succ (Syn.var 0))))
      = Tm.prc (Tm.succ (Syn.var 0)) (shift (code f))
          (Syn.subst (up (up (fun i => Syn.var i.succ))) (code g)) := by
    rw [sigma_app, sigma_repl, sigma_succ, sigma_var, code_prec, Tm.subst_prc,
      Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift, Syn.subst_up_up_repl_up_up_shift]
  have e : (fun j => sigma ((Fin.cases (Syn.var 0)
        (repl (PTm.app (.prec f g) Syn.var)) : Fin (k + 2) → PTm (k + 1)) j))
      = fun j => Syn.subst
          (Fin.cases (Syn.var 0) (Fin.cases (code (.prec f g)) Syn.var))
          ((up (up (fun i => Syn.var i.succ)) : Fin (k + 2) → Tm (k + 3)) j) := by
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
    · simp only [Fin.cases_zero, sigma_var, Syn.up_zero, Syn.subst_var]
    · simp only [Fin.cases_succ, Fin.cases_zero, Syn.repl_zero, sigma_app_var, Syn.up_succ,
        Syn.up_zero, Syn.shift_var, Syn.subst_var]
    · simp only [Fin.cases_succ, Syn.repl_succ, sigma_var, Syn.up_succ, Syn.shift_var,
        Syn.subst_var]
  have e2 : sigma (PTm.app g
        (Fin.cases (Syn.var 0) (repl (PTm.app (.prec f g) Syn.var))))
      = Syn.subst (Fin.cases (Syn.var 0) (Fin.cases (code (.prec f g)) Syn.var))
          (Syn.subst (up (up (fun i => Syn.var i.succ))) (code g)) := by
    rw [sigma_app, Syn.subst_subst, e]
  rw [e1, e2]
  exact Q.prc_succ _ _ _

theorem ax_succNeZero :
    [] ⊢[TeqAx] ((Tm.succ (Syn.var 0) ≐ Tm.zero : Fm Tm 1) ⟶ Fm.bot) := by
  refine Prf.impI ?_
  have h : Q.succ (Q.mk [(Tm.succ (Syn.var 0) ≐ Tm.zero : Fm Tm 1)] (Syn.var 0)) = 0 :=
    Q.sound Prf.hyp0
  exact Prf.impE Teq.sep (Q.exact (Q.absurd_succ h (Q.mk _ Tm.zero) (Q.mk _ (Tm.succ Tm.zero))))

theorem ax_succInj :
    [] ⊢[TeqAx] ((Tm.succ (Syn.var 0) ≐ Tm.succ (Syn.var 1) : Fm Tm 2)
      ⟶ (Syn.var 0 ≐ Syn.var 1)) := by
  refine Prf.impI ?_
  have h : Q.succ (Q.mk [(Tm.succ (Syn.var 0) ≐ Tm.succ (Syn.var 1) : Fm Tm 2)] (Syn.var 0))
      = Q.succ (Q.mk _ (Syn.var 1)) := Q.sound Prf.hyp0
  exact Q.exact (Q.succ_inj h)

theorem ax_ind (φ : Fm PTm (n + 1)) (h : φ.QF) :
    [] ⊢[TeqAx] ((φ.subst (inst PTm.zero) ⟶
      Fm.all (φ ⟶ φ.subst (repl (PTm.succ (Syn.var 0)))) ⟶ Fm.all φ).map morph.f) :=
  Prf.iffMpr (morph.map_ind φ PTm.zero (PTm.succ (Syn.var 0)) [])
    (Teq.qfInd (φ.map morph.f) (Fm.map_QF _ h))

/-- The interpretation of `iPRA` in `T_eq`: function symbols become terms, and
every axiom of `iPRA` becomes a theorem. -/
def interp : Interp PRAAx TeqAx where
  toTmMorph := morph
  f_ax := by
    intro k φ hφ
    cases hφ with
    | proj i => exact ax_proj i
    | comp f gs => exact ax_comp f gs
    | precZero f g => exact ax_precZero f g
    | precSucc f g => exact ax_precSucc f g
    | succNeZero => exact ax_succNeZero
    | succInj => exact ax_succInj
    | ind φ h => exact ax_ind φ h

end FromPRA

end LeanProofs.ConciseIPRA
