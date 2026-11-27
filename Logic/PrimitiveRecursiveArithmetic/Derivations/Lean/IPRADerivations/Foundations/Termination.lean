import IPRADerivations.Algebra.CubeRootTwo
import IPRADerivations.Core.Header

/-!
# Termination of measure-decreasing runs (`ipra_unified_finitary_framework_2026-11-15`)

The framework packets bound loops by an explicit fuel: if a step function strictly
decreases a measure `m` on every non-terminal state, then a run from `s₀` reaches
a terminal state within `m(s₀) + 1` steps (`paper/sections/04_booleanization.tex`).

For arbitrary unary primitive recursive symbols `done`, `step` and `m`, write
`dn(s) = sg(done s) ∈ {0, 1}` for "terminal", and let the stopped run be
`r₀ = s₀`, `r_{k+1} = r_k` if `dn(r_k) = 1` and `step(r_k)` otherwise. Derived in iPRA:

  `(∀ s, dn(s) = 0 → m(step s) < m(s)) → dn(r_{m(s₀)+1}) = 1`.

The proof is quantifier-free induction on `k`, under the universal hypothesis, for
the invariant `dn(r_k) = 1 ∨ m(r_k) + k ≤ m(s₀)`.
-/

namespace LeanProofs.IPRA.Foundations.Termination

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)

variable (done step m : PR 1) {n : ℕ} {Γ : List (Fm PTm n)}

/-- `dn(s) = sg(done s)`. -/
abbrev dn (s : PTm n) : PTm n := sg (ap1 done s)

/-- The step of the stopped run; variables `0 = k`, `1 = r_k`, `2 = s₀`. -/
abbrev runStep : PTm 3 :=
  dn done (var 1) * var 1 + monus one (dn done (var 1)) * ap1 step (var 1)

/-- `r(k, s₀)`. -/
abbrev runF : PR 2 := rec2 (var 0) (runStep done step)
abbrev r (k s₀ : PTm n) : PTm n := ap2 (runF done step) k s₀

/-- The decrease hypothesis, as a closed formula. -/
abbrev decrease : Fm PTm n :=
  Fm.all ((dn done (var 0) ≐ zero) ⟶ lt (ap1 m (ap1 step (var 0))) (ap1 m (var 0)))

/-- The invariant; variables `0 = k`, `1 = s₀`. -/
abbrev invariant : Fm PTm 2 :=
  (dn done (r done step (var 0) (var 1)) ≐ one) ⋎
    le (ap1 m (r done step (var 0) (var 1)) + var 0) (ap1 m (var 1))

/-- `dn(r_{m(s₀)+1}) = 1` under the decrease hypothesis; variable `0 = s₀`. -/
abbrev terminationFormula : Fm PTm 1 :=
  decrease done step m ⟶ (dn done (r done step (succ (ap1 m (var 0))) (var 0)) ≐ one)

/-- The context of the induction step. -/
abbrev Δ : List (Fm PTm 2) := [invariant done step m, decrease done step m]

/-- `R = r(k, s₀)` and `R' = r(k + 1, s₀)` over the variables `0 = k`, `1 = s₀`. -/
abbrev R : PTm 2 := r done step (var 0) (var 1)
abbrev R' : PTm 2 := r done step (succ (var 0)) (var 1)

variable {done step m}

theorem r_zero (s₀ : PTm n) : Γ ⊢[PRAAx] r done step zero s₀ ≐ s₀ := by
  simpa using rec2_zero (Γ := Γ) (var 0) (runStep done step) s₀

theorem r_succ (k s₀ : PTm n) :
    Γ ⊢[PRAAx] r done step (succ k) s₀ ≐ dn done (r done step k s₀) * r done step k s₀
      + monus one (dn done (r done step k s₀)) * ap1 step (r done step k s₀) := by
  have h := rec2_succ (Γ := Γ) (var 0) (runStep done step) k s₀
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap1, Syn.subst_var,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  exact h

theorem sg_cases (x : PTm n) : Γ ⊢[PRAAx] (sg x ≐ zero) ⋎ (sg x ≐ one) := by
  refine .orE (zero_or_succ x) ?_ ?_
  · exact .orI₁ ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero)
  · exact .orI₂ ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (sg_succ _))

theorem shift_decrease : Fm.shift (decrease done step m (n := n)) = decrease done step m (n := n + 1) := by
  simp [Fm.shift, decrease]

/-- The decrease hypothesis at a term. -/
theorem decrease_at {Δ : List (Fm PTm n)} (h : Δ ⊢[PRAAx] decrease done step m) (s : PTm n) :
    Δ ⊢[PRAAx] (dn done s ≐ zero) ⟶ lt (ap1 m (ap1 step s)) (ap1 m s) := by
  simpa using Prf.allE s h

theorem step_case : Δ done step m ⊢[PRAAx]
    (dn done (R' done step) ≐ one) ⋎ le (ap1 m (R' done step) + succ (var 0)) (ap1 m (var 1)) := by
  have hR' := r_succ (Γ := Δ done step m) (done := done) (step := step) (var 0) (var 1)
  refine .orE (sg_cases (ap1 done (R done step))) ?_ ?_
  · -- dn R = 0: R' = step R.
    have eR : _ ⊢[PRAAx] R' done step ≐ ap1 step (R done step) :=
      hR'.wk.eqTrans ((congrAdd (congrMul Prf.hyp0 (.eqRefl _))
        (congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)) (.eqRefl _))).eqTrans
        ((congrAdd (zero_mul _) (one_mul _)).eqTrans (zero_add _)))
    refine .orE (Prf.hyp1 : _ ⊢[PRAAx] invariant done step m) ?_ ?_
    · exact .botE _ (succ_ne_zero (a := zero) (Prf.hyp0.eqSymm.eqTrans Prf.hyp1))
    · have hD : Δ done step m ⊢[PRAAx] decrease done step m := Prf.hyp1
      have hlt : (le (ap1 m (R done step) + var 0) (ap1 m (var 1)) :: (dn done (R done step) ≐ zero) ::
          Δ done step m) ⊢[PRAAx] lt (ap1 m (ap1 step (R done step))) (ap1 m (R done step)) :=
        Prf.impE (decrease_at hD.wk.wk (R done step)) Prf.hyp1
      refine .orI₂ (le_congr (a := succ (ap1 m (ap1 step (R done step))) + var 0) ?_ (.eqRefl _)
        (le_trans (add_le_add_right (var 0) hlt) Prf.hyp0))
      refine (succ_add _ _).eqTrans ((add_succ _ _).eqSymm.eqTrans ?_)
      exact congrAdd (congrAp1 m eR.wk).eqSymm (.eqRefl _)
  · -- dn R = 1: R' = R.
    have eR : _ ⊢[PRAAx] R' done step ≐ R done step :=
      hR'.wk.eqTrans ((congrAdd (congrMul Prf.hyp0 (.eqRefl _))
        (congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)) (.eqRefl _))).eqTrans
        ((congrAdd (one_mul _) (zero_mul _)).eqTrans (add_zero _)))
    refine .orI₁ (.eqTrans ?_ Prf.hyp0)
    exact congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrAp1 done eR))

theorem termination : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (terminationFormula done step m) := by
  refine closeUniv 1 (.impI ?_)
  have hall : [decrease done step m] ⊢[PRAAx] Fm.all (invariant done step m) := by
    refine PRA.qfInd _ ⟨trivial, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_or, Fm.subst_eq, subst_le, PTm.subst_add, PTm.subst_monus, subst_ap1,
        subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_succ, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ, Fin.succ_zero_eq_one]
      refine .orI₂ (le_congr ?_ (.eqRefl _) (le_refl _))
      exact (congrAp1 m (r_zero _)).eqSymm.eqTrans (add_zero _).eqSymm
    · simp only [Fm.subst_or, Fm.subst_eq, subst_le, PTm.subst_add, PTm.subst_monus, subst_ap1,
        subst_ap2, Syn.subst_var, Syn.repl_zero, Syn.repl_succ, repl_one,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, List.map_cons, List.map_nil,
        shift_decrease]
      exact step_case
  have h := Prf.allE (succ (ap1 m (var 0))) hall
  simp only [Fm.subst_or, Fm.subst_eq, subst_le, PTm.subst_add, PTm.subst_monus, subst_ap1,
    subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_succ, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ, Fin.succ_zero_eq_one] at h
  refine .orE h Prf.hyp0 ?_
  exact not_succ_le_self _ _ (le_trans (le_add_left _ _) Prf.hyp0)

end LeanProofs.IPRA.Foundations.Termination
