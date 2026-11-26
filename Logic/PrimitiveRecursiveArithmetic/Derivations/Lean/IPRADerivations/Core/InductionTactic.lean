import IPRADerivations.Core.Basic

/-!
# Induction with the substitutions pushed through

`ind φ hφ h0 hS` derives a quantifier-free `φ` over `k + 1` variables in the empty context from the base case
`φ[0]` and the step `φ ⊢ φ[succ (var 0)]`. Both goals come with the substitution written as
`φ.subst (Syn.inst zero)` and `φ.subst (repl (succ (var 0)))`, and every use pushed it through the formula by a
`simp only` list of its own. `ipra_ind` does both steps:

    ipra_ind                       -- `φ.QF` by `trivial`
    ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]

leaves the base case and the step, in this order, with the substitutions pushed through equations, connectives,
`+`, `*`, `monus`, `pred`, numerals and variables; the bracket adds the substitution lemmas of the other symbols
that occur.
-/

/-- `ipra_ind (hQF) [l₁, …]`: quantifier-free induction on variable `0`, leaving the base case and the step with
the substitutions pushed through the formula. -/
syntax "ipra_ind" (" (" term ")")? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_ind) => `(tactic| ipra_ind (trivial))
  | `(tactic| ipra_ind [$ls,*]) => `(tactic| ipra_ind (trivial) [$ls,*])
  | `(tactic| ipra_ind ($qf)) =>
    `(tactic| (refine LeanProofs.IPRA.ind _ $qf ?_ ?_ <;>
        simp only [LeanProofs.ConciseIPRA.Fm.subst_eq, LeanProofs.ConciseIPRA.Fm.subst_imp,
          LeanProofs.ConciseIPRA.Fm.subst_and, LeanProofs.ConciseIPRA.Fm.subst_or,
          LeanProofs.IPRA.PTm.subst_add, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
          LeanProofs.IPRA.PTm.subst_pred, LeanProofs.IPRA.PTm.subst_num,
          LeanProofs.ConciseIPRA.PTm.subst_zero, LeanProofs.ConciseIPRA.PTm.subst_succ,
          LeanProofs.ConciseIPRA.Syn.subst_var, LeanProofs.ConciseIPRA.Syn.inst_zero,
          LeanProofs.ConciseIPRA.Syn.inst_one, LeanProofs.IPRA.inst_two, LeanProofs.IPRA.inst_three,
          LeanProofs.IPRA.inst_four, LeanProofs.ConciseIPRA.Syn.repl_zero, LeanProofs.IPRA.repl_one,
          LeanProofs.IPRA.repl_two, LeanProofs.IPRA.repl_three, LeanProofs.IPRA.repl_four]))
  | `(tactic| ipra_ind ($qf) [$ls,*]) =>
    `(tactic| (refine LeanProofs.IPRA.ind _ $qf ?_ ?_ <;>
        simp only [$ls,*, LeanProofs.ConciseIPRA.Fm.subst_eq, LeanProofs.ConciseIPRA.Fm.subst_imp,
          LeanProofs.ConciseIPRA.Fm.subst_and, LeanProofs.ConciseIPRA.Fm.subst_or,
          LeanProofs.IPRA.PTm.subst_add, LeanProofs.IPRA.PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
          LeanProofs.IPRA.PTm.subst_pred, LeanProofs.IPRA.PTm.subst_num,
          LeanProofs.ConciseIPRA.PTm.subst_zero, LeanProofs.ConciseIPRA.PTm.subst_succ,
          LeanProofs.ConciseIPRA.Syn.subst_var, LeanProofs.ConciseIPRA.Syn.inst_zero,
          LeanProofs.ConciseIPRA.Syn.inst_one, LeanProofs.IPRA.inst_two, LeanProofs.IPRA.inst_three,
          LeanProofs.IPRA.inst_four, LeanProofs.ConciseIPRA.Syn.repl_zero, LeanProofs.IPRA.repl_one,
          LeanProofs.IPRA.repl_two, LeanProofs.IPRA.repl_three, LeanProofs.IPRA.repl_four]))
