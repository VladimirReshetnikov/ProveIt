import IPRADerivations.Core.Basic

/-!
# Induction with the substitutions pushed through

Quantifier-free induction on variable `0` comes in two forms.

* `ind φ hφ h0 hS` derives `φ` over `k + 1` variables in the empty context from the base case `φ[0]` and the step
  `φ ⊢ φ[succ (var 0)]`.
* `PRA.qfInd φ hφ h0 hS` derives `∀ φ` in a context `Γ` from the base case `Γ ⊢ φ[0]` and the step
  `φ, Γ↑ ⊢ φ[succ (var 0)]`.

Both goals come with the substitution written as `φ.subst (Syn.inst zero)` and `φ.subst (repl (succ (var 0)))`,
and every use pushed it through the formula by a `simp only` list of its own. The tactics do both steps:

    ipra_ind                       -- `ind`, `φ.QF` by `trivial`
    ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
    ipra_qfind (le_QF _ _) [subst_law]      -- `PRA.qfInd`

leave the base case and the step, in this order, with the substitutions pushed through equations, connectives,
`+`, `*`, `monus`, `pred`, numerals and variables (for `ipra_qfind` also through the shifted parameters); the
bracket adds the substitution lemmas of the other symbols that occur.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open ConciseIPRA.PTm (succ)

/-- A shifted parameter is unchanged by the step substitution. -/
@[simp] theorem subst_repl_shift {n : ℕ} (s : PTm (n + 1)) (t : PTm n) :
    Syn.subst (repl s) (Syn.shift t) = Syn.shift t := by
  rw [Syn.subst_shift]; simp only [Syn.repl_succ]; rfl

end LeanProofs.IPRA

/-- The substitution lemmas shared by `ipra_ind` and `ipra_qfind`. -/
syntax "ipra_ind_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_ind_simp) =>
    `(tactic| simp only [LeanProofs.ConciseIPRA.Fm.subst_eq, LeanProofs.ConciseIPRA.Fm.subst_imp,
        LeanProofs.ConciseIPRA.Fm.subst_and, LeanProofs.ConciseIPRA.Fm.subst_or,
        LeanProofs.IPRA.PTm.subst_add, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
        LeanProofs.IPRA.PTm.subst_pred, LeanProofs.IPRA.PTm.subst_num,
        LeanProofs.ConciseIPRA.PTm.subst_zero, LeanProofs.ConciseIPRA.PTm.subst_succ,
        LeanProofs.ConciseIPRA.Syn.subst_var, LeanProofs.ConciseIPRA.Syn.inst_zero,
        LeanProofs.ConciseIPRA.Syn.inst_one, LeanProofs.IPRA.inst_two, LeanProofs.IPRA.inst_three,
        LeanProofs.IPRA.inst_four, LeanProofs.ConciseIPRA.Syn.repl_zero, LeanProofs.IPRA.repl_one,
        LeanProofs.IPRA.repl_two, LeanProofs.IPRA.repl_three, LeanProofs.IPRA.repl_four])
  | `(tactic| ipra_ind_simp [$ls,*]) =>
    `(tactic| simp only [$ls,*, LeanProofs.ConciseIPRA.Fm.subst_eq, LeanProofs.ConciseIPRA.Fm.subst_imp,
        LeanProofs.ConciseIPRA.Fm.subst_and, LeanProofs.ConciseIPRA.Fm.subst_or,
        LeanProofs.IPRA.PTm.subst_add, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
        LeanProofs.IPRA.PTm.subst_pred, LeanProofs.IPRA.PTm.subst_num,
        LeanProofs.ConciseIPRA.PTm.subst_zero, LeanProofs.ConciseIPRA.PTm.subst_succ,
        LeanProofs.ConciseIPRA.Syn.subst_var, LeanProofs.ConciseIPRA.Syn.inst_zero,
        LeanProofs.ConciseIPRA.Syn.inst_one, LeanProofs.IPRA.inst_two, LeanProofs.IPRA.inst_three,
        LeanProofs.IPRA.inst_four, LeanProofs.ConciseIPRA.Syn.repl_zero, LeanProofs.IPRA.repl_one,
        LeanProofs.IPRA.repl_two, LeanProofs.IPRA.repl_three, LeanProofs.IPRA.repl_four])

/-- `ipra_ind (hQF) [l₁, …]`: quantifier-free induction on variable `0` in the empty context, leaving the base
case and the step with the substitutions pushed through the formula. -/
syntax "ipra_ind" (" (" term ")")? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_ind) => `(tactic| ipra_ind (trivial))
  | `(tactic| ipra_ind [$ls,*]) => `(tactic| ipra_ind (trivial) [$ls,*])
  | `(tactic| ipra_ind ($qf)) => `(tactic| (refine LeanProofs.IPRA.ind _ $qf ?_ ?_ <;> ipra_ind_simp))
  | `(tactic| ipra_ind ($qf) [$ls,*]) =>
    `(tactic| (refine LeanProofs.IPRA.ind _ $qf ?_ ?_ <;> ipra_ind_simp [$ls,*]))

/-- `ipra_qfind (hQF) [l₁, …]`: quantifier-free induction on variable `0` in a context (`PRA.qfInd`), leaving
the base case and the step with the substitutions pushed through the formula and the shifted parameters. -/
syntax "ipra_qfind" (" (" term ")")? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_qfind) => `(tactic| ipra_qfind (trivial))
  | `(tactic| ipra_qfind [$ls,*]) => `(tactic| ipra_qfind (trivial) [$ls,*])
  | `(tactic| ipra_qfind ($qf)) =>
    `(tactic| (refine LeanProofs.ConciseIPRA.PRA.qfInd _ $qf ?_ ?_ <;>
        ipra_ind_simp [LeanProofs.ConciseIPRA.Syn.subst_inst_shift, LeanProofs.IPRA.subst_repl_shift]))
  | `(tactic| ipra_qfind ($qf) [$ls,*]) =>
    `(tactic| (refine LeanProofs.ConciseIPRA.PRA.qfInd _ $qf ?_ ?_ <;>
        ipra_ind_simp [$ls,*, LeanProofs.ConciseIPRA.Syn.subst_inst_shift, LeanProofs.IPRA.subst_repl_shift]))
