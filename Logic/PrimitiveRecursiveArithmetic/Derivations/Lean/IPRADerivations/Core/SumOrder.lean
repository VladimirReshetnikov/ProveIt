import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination

/-!
# Comparing sums with different parameters

* `add_le_add₂`: `a ≤ b` and `c ≤ d` give `a + c ≤ b + d`;
* `sum_le_params`: if `f(i, x) ≤ g(i, y)` for `i < N`, then
  `∑_{i<N} f(i, x) ≤ ∑_{i<N} g(i, y)`. Unlike `Analysis/PowerSums.sum_le`, the two sums may read
  different parameters, which is what is needed to compare one body at two thresholds.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem add_le_add₂ {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a + c) (b + d) := by
  refine le_of_eq_add (d := monus b a + monus d c) ?_
  ipra_lc natEq (eq_add_of_le h₁) + natEq (eq_add_of_le h₂)

/-- Sums of pointwise smaller bodies are smaller, with possibly different parameters. -/
theorem sum_le_params (f g : PTm 2) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N y) := by
  let P := le (ap2 (sumF f) (var 0) (Syn.shift x)) (ap2 (sumF g) (var 0) (Syn.shift y))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P] using le_congr (sum_zero (Γ := Γ) f x).eqSymm (sum_zero g y).eqSymm (le_refl zero)
    · simp only [P, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact .impI (le_congr (sum_succ' f (var 0) _).eqSymm (sum_succ' g (var 0) _).eqSymm
        (add_le_add₂ Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)))
  simpa [P] using atBound

/-- Summing the constant body that reads its parameter gives the length times that parameter. -/
theorem sum_const_param (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (var 1 : PTm 2)) N L ≐ N * L := by
  have all : Γ ⊢[PRAAx] Fm.all
      (ap2 (sumF (var 1 : PTm 2)) (var 0) (Syn.shift L) ≐ var 0 * Syn.shift L) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (sum_zero _ _).eqTrans (zero_mul _).eqSymm
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact (sum_succ' _ _ _).eqTrans
        ((congrAdd Prf.hyp0 (by simp [inst2]; exact .eqRefl _)).eqTrans (succ_mul _ _).eqSymm)
  simpa using all.allE N

/-- A sum of `N` terms bounded above by `L` is bounded by `N * L`. -/
theorem sum_le_uniform_bound (f : PTm 2) {N L x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (Syn.shift L))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (N * L) := by
  refine le_congr (.eqRefl _) (sum_const_param N L) (sum_le_params f (var 1) x L N ?_)
  simpa [inst2] using h

/-- A sum of `N` terms bounded below by `L` is at least `N * L`. -/
theorem uniform_bound_le_sum (f : PTm 2) {N L x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift L) (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (N * L) (ap2 (sumF f) N x) := by
  refine le_congr (sum_const_param N L) (.eqRefl _) (sum_le_params (var 1) f L x N ?_)
  simpa [inst2] using h

/-- Each summand at least one gives a lower bound by the number of terms. -/
theorem le_sum_of_one_le (f : PTm 2) {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le one (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le N (ap2 (sumF f) N x) :=
  le_congr (by ipra_ring) (.eqRefl _)
    (uniform_bound_le_sum (L := one) f (by simpa [Syn.shift] using h))

/-- The sum of a body that always returns one is its length. -/
theorem sum_one_body (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (one : PTm 2)) N x ≐ N := by
  refine (sum_congr_bounded (one : PTm 2) (var 1) x one N (.allI (.impI ?_))).eqTrans
    ((sum_const_param N one).eqTrans (by ipra_ring))
  simp [inst2, Syn.shift]
  exact .eqRefl _

private theorem weighted_sum_pair_zero (f g : PTm 2) (a b x y : PTm n) :
    Γ ⊢[PRAAx] a * ap2 (sumF f) zero x + b * ap2 (sumF g) zero y ≐ zero :=
  (congrAdd ((congrMul (.eqRefl _) (sum_zero f x)).eqTrans (mul_zero a))
    ((congrMul (.eqRefl _) (sum_zero g y)).eqTrans (mul_zero b))).eqTrans (add_zero _)

private theorem weighted_sum_pair_succ (f g : PTm 2) (a b x y j : PTm n) :
    Γ ⊢[PRAAx] a * ap2 (sumF f) (succ j) x + b * ap2 (sumF g) (succ j) y ≐
      (a * ap2 (sumF f) j x + b * ap2 (sumF g) j y) +
        (a * inst2 f j x + b * inst2 g j y) :=
  (congrAdd (congrMul (.eqRefl _) (sum_succ' f j x))
    (congrMul (.eqRefl _) (sum_succ' g j y))).eqTrans (by ipra_ring)

/-- Sum an inequality between two weighted pairs with independent parameters. -/
theorem sum_weighted_pair_le (f1 f2 g1 g2 : PTm 2) (a b c d x1 x2 y1 y2 N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f1 (var 0) (Syn.shift x1) + Syn.shift b * inst2 f2 (var 0) (Syn.shift x2))
        (Syn.shift c * inst2 g1 (var 0) (Syn.shift y1) + Syn.shift d * inst2 g2 (var 0) (Syn.shift y2)))) :
    Γ ⊢[PRAAx] le (a * ap2 (sumF f1) N x1 + b * ap2 (sumF f2) N x2)
      (c * ap2 (sumF g1) N y1 + d * ap2 (sumF g2) N y2) := by
  let P : Fm PTm (n + 1) :=
    le (Syn.shift a * ap2 (sumF f1) (var 0) (Syn.shift x1) +
        Syn.shift b * ap2 (sumF f2) (var 0) (Syn.shift x2))
      (Syn.shift c * ap2 (sumF g1) (var 0) (Syn.shift y1) +
        Syn.shift d * ap2 (sumF g2) (var 0) (Syn.shift y2))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P] using le_congr (weighted_sum_pair_zero (Γ := Γ) f1 f2 a b x1 x2).eqSymm
        (weighted_sum_pair_zero g1 g2 c d y1 y2).eqSymm (le_refl zero)
    · simp only [P, subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      refine .impI (le_congr (weighted_sum_pair_succ f1 f2 _ _ _ _ (var 0)).eqSymm
        (weighted_sum_pair_succ g1 g2 _ _ _ _ (var 0)).eqSymm ?_)
      exact add_le_add₂ Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)
  simpa [P] using atBound

/-- The weighted pair inequality when the left side has one summand. -/
theorem sum_scaled_le_weighted_pair (f g1 g2 : PTm 2) (a c d x y1 y2 N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f (var 0) (Syn.shift x))
        (Syn.shift c * inst2 g1 (var 0) (Syn.shift y1) + Syn.shift d * inst2 g2 (var 0) (Syn.shift y2)))) :
    Γ ⊢[PRAAx] le (a * ap2 (sumF f) N x)
      (c * ap2 (sumF g1) N y1 + d * ap2 (sumF g2) N y2) := by
  refine le_congr ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)) (.eqRefl _)
    (sum_weighted_pair_le f f g1 g2 a zero c d x x y1 y2 N (.allI (.impI ?_)))
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
  exact le_congr ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)).eqSymm (.eqRefl _)
    (.impE h.allOpen.wk Prf.hyp0)

end LeanProofs.IPRA
