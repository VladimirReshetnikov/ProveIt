import ConciseIPRA.NativeEq

/-!
# Uniqueness of iteration is a derived rule

The package `Research/scalar_uniqueness` proposes to replace induction for
literal equations by one uniqueness rule,

  from `Γ ⊢ f(S z) = h(f(z))` with `z` fresh infer `Γ ⊢ f(t) = I(t, f(0); u.h(u))`.

Its premise has no induction hypothesis, and the seed is determined by `f`.
This module proves the easy half of the proposed equivalence: the rule is a
derived rule of the kernel (`NPrf.uniq`), by one equation induction.  The
converse, that the rule recovers equation induction in the absence of an
induction rule, is the content of the report and is not formalized here.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ} {Γ : List (NFm n)}

/-- **Orbit closure**: a term that satisfies the recursion of an iterator is
that iterator at every count.  The conclusion is a closure and no target term
is supplied; this is the rule Orbit of the package `orbit_closure`, in its
native form. -/
theorem NPrf.orbit (f h : Tm (n + 1))
    (step : NPrf (Γ.map NFm.shift)
      (.eq (Syn.subst (repl (succ (Syn.var 0))) f)
        (Syn.subst (inst f) (Syn.subst (up (fun i => Syn.var i.succ)) h)))) :
    NPrf Γ (.Q (.eq f (iter (Syn.var 0) (Syn.shift (Syn.subst (inst zero) f))
      (Syn.subst (up (fun i => Syn.var i.succ)) h)))) := by
  refine .qIInd _ _ ?_
  have e : Syn.subst (up (repl (succ (Syn.var 0))))
      (Syn.subst (up (fun i => (Syn.var i.succ : Tm (n + 1)))) h)
      = Syn.subst (up (fun i => Syn.var i.succ)) h := by
    rw [Syn.subst_subst, Syn.up_comp]
    exact congrArg (fun ρ => Syn.subst (up ρ) h) (funext fun i => by simp)
  simp only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift, e]
  exact eqTrans step.wk (eqTrans (eqCongr _ hyp0) (eqSymm (.iterSucc _ _ _)))

/-- Uniqueness of iteration: a term that satisfies the recursion of an iterator
is that iterator.  It is the orbit closure used at the target `t` by `QE`. -/
theorem NPrf.uniq (f h : Tm (n + 1)) (t : Tm n)
    (step : NPrf (Γ.map NFm.shift)
      (.eq (Syn.subst (repl (succ (Syn.var 0))) f)
        (Syn.subst (inst f) (Syn.subst (up (fun i => Syn.var i.succ)) h)))) :
    NPrf Γ (.eq (Syn.subst (inst t) f) (iter t (Syn.subst (inst zero) f) h)) := by
  have h0 : NPrf Γ ((NFm.eq f (iter (Syn.var 0) (Syn.shift (Syn.subst (inst zero) f))
      (Syn.subst (up (fun i => Syn.var i.succ)) h))).subst (inst zero)) := by
    simp only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      Syn.subst_up_inst_up_shift]
    exact eqSymm (.iterZero _ _)
  have key := NPrf.qE t (NPrf.orbit f h step) h0
  simpa only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] using key

end LeanProofs.ConciseIPRA
