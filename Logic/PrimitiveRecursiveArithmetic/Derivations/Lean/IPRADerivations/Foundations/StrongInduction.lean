import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Order

/-!
# Strong induction for a violation term

Framework layer (first use: the weight bound of the Selberg sieve,
`AnalyticNumberTheory/SieveWeightBound`).

iPRA has induction for quantifier-free formulas only, so the hypothesis "the claim holds for all `i < N`" of strong
(course-of-values) induction cannot be stated with a quantifier. It can be stated as an equation: a claim about `N`
and a parameter `x` is given by a *violation term* `v(N, x)` (a body over `0 = N`, `1 = x`) that vanishes exactly
when the claim holds, and "the claim holds for all `i < N`" is `Σ_{i<N} v(i, x) = 0`.

* `strong_ind`: if `Σ_{i<N} v(i, x) = 0` gives `v(N, x) = 0` for all `N`, `x` (in every context), then
  `v(N, x) = 0` for all `N`, `x`.

For a claim `a(N, x) ≤ b(N, x)` the violation term is `a ∸ b` itself, since `le a b` is `a ∸ b = 0`; for an
equation it is `1 ∸ [a = b]`. A side condition `c(x)` on the parameter, which a step function quantified over all
contexts cannot assume, is put into the term as a factor `[c(x)]`.

The pattern was used ad hoc before (`AnalyticNumberTheory/EulerProduct`, with the violation term
`1 ∸ [LHS = RHS]`); `sum_zero_elim` recovers the induction hypothesis at each `i < N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev siF (v : PTm 2) : Fm PTm 2 := ap2 (sumF v) (var 0) (var 1) ≐ zero

private theorem strong_sum (v : PTm 2)
    (step : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (N x : PTm k),
      (Δ ⊢[PRAAx] ap2 (sumF v) N x ≐ zero) → (Δ ⊢[PRAAx] inst2 v N x ≐ zero)) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] siF v := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero]
    exact sum_zero _ _
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 (step _ _ Prf.hyp0)).eqTrans (add_zero _))

/-- Strong induction: if the vanishing of all violations below `N` gives the vanishing of the violation at `N`,
then every violation vanishes. -/
theorem strong_ind (v : PTm 2)
    (step : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (N x : PTm k),
      (Δ ⊢[PRAAx] ap2 (sumF v) N x ≐ zero) → (Δ ⊢[PRAAx] inst2 v N x ≐ zero))
    (N x : PTm n) : Γ ⊢[PRAAx] inst2 v N x ≐ zero := by
  have h := inst (Γ := Γ) (strong_sum v step) (![succ N, x] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact sum_zero_elim v h ((succ_monus_succ _ _).eqTrans (le_refl N))

end LeanProofs.IPRA
