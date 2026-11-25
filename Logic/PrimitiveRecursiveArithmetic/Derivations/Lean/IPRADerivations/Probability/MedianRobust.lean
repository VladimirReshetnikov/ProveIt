import IPRADerivations.Probability.MedianSymmetry
import IPRADerivations.Core.LinearCombination

/-!
# Rank perturbation and the median envelope, by counting

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:rank-perturbation` and the
corollary "median rank envelope", in count form. Two samples `x(i, p)` and `z(i, p)` of length `N`
differ in `R = #{i < N : x_i ≠ z_i}` coordinates. The bounded pigeonhole argument of the packet
(at most `R` of the entries below a threshold can be replacements) is the pointwise estimate
`[z < t] ≤ [x < t] + [x ≠ z]`, summed:

* `below_perturb`, `above_perturb`: `B_z(t) ≤ B_x(t) + R` and `A_z(t) ≤ A_x(t) + R`;
* `robust_median`: if `2(B_x(t) + R) ≤ N` and `2(A_x(t) + R) ≤ N`, then `t` is still a balance
  median of `z`: a median that is `R` ranks away from both sides survives any `R` replacements.

With `x_{(k)}` the `k`-th order statistic, `B_x(t) ≤ k − R` for `t ≤ x_{(k−R)}`, so the count form
gives `x_{(k−R)} ≤ z_{(k)}`; the order statistics themselves are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianRobust

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Probability.MedianWeighted (wL)
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Pointwise -/

theorem le_of_ne {u v x z : PTm n} (h : Γ ⊢[PRAAx] eqb x z ≐ zero) (hu : Γ ⊢[PRAAx] le u one) :
    Γ ⊢[PRAAx] le u (v + monus one (eqb x z)) := by
  refine le_trans hu (le_of_eq_add (d := v) ?_)
  ipra_lc natEq ((congrMonus (.eqRefl one) h).eqTrans (monus_zero one))

theorem le_of_same {u v x z : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx] le u (v + monus one (eqb x z)) :=
  le_of_eq_add (d := monus one (eqb x z)) (congrAdd h.eqSymm (.eqRefl _))

/-- `[z < t] ≤ [x < t] + [x ≠ z]`. -/
theorem below_bit_perturb (x z t : PTm n) :
    Γ ⊢[PRAAx] le (sg (monus t z)) (sg (monus t x) + monus one (eqb x z)) := by
  refine .orE (lt_or_le x z) (le_of_ne (eqb_zero_of_lt Prf.hyp0) (sg_le_one _))
    (.orE (lt_or_eq_of_le Prf.hyp0) (le_of_ne (eqb_zero_of_gt Prf.hyp0) (sg_le_one _)) ?_)
  exact le_of_same (congrSg (congrMonus (.eqRefl t) Prf.hyp0))

/-- `[t < z] ≤ [t < x] + [x ≠ z]`. -/
theorem above_bit_perturb (x z t : PTm n) :
    Γ ⊢[PRAAx] le (sg (monus z t)) (sg (monus x t) + monus one (eqb x z)) := by
  refine .orE (lt_or_le x z) (le_of_ne (eqb_zero_of_lt Prf.hyp0) (sg_le_one _))
    (.orE (lt_or_eq_of_le Prf.hyp0) (le_of_ne (eqb_zero_of_gt Prf.hyp0) (sg_le_one _)) ?_)
  exact le_of_same (congrSg (congrMonus Prf.hyp0 (.eqRefl t)))

/-! ## Counts -/

section Samples

variable (X Z : PTm 2)

/-- `[x_i ≠ z_i]`. -/
def diffB : PTm 2 := monus one (eqb X Z)

theorem inst2_diff (i p : PTm n) : inst2 (diffB X Z) i p = monus one (eqb (inst2 X i p) (inst2 Z i p)) := by
  simp [inst2, diffB]

/-- `R = #{i < N : x_i ≠ z_i}`. -/
abbrev Rd (N p : PTm n) : PTm n := ap2 (sumF (diffB X Z)) N p

theorem diff_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL (diffB X Z)) i (pairT t p) ≐ monus one (eqb (inst2 X i p) (inst2 Z i p)) := by
  have e : inst2 (wL (diffB X Z)) i (pairT t p) = inst2 (diffB X Z) i (sndT (pairT t p)) :=
    subst_data i (pairT t p) (diffB X Z)
  rw [e, inst2_diff]
  exact congrMonus (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb
    (congrInst2 X (.eqRefl _) (snd_pair _ _)) (congrInst2 Z (.eqRefl _) (snd_pair _ _)))

theorem diff_sum (N t p : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (wL (diffB X Z))) N (pairT t p) ≐ Rd X Z N p := by
  refine sum_congr_bounded _ _ _ _ N (.allI (.impI ?_))
  rw [shift_pairT', inst2_diff]
  exact diff_pt X Z _ _ _

/-- `B_z(t) ≤ B_x(t) + R`. -/
theorem below_perturb (N t p : PTm n) : Γ ⊢[PRAAx] le (Bc Z N t p) (Bc X N t p + Rd X Z N p) := by
  refine le_congr (.eqRefl _) ((sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) (diff_sum X Z N t p)))
    (sum_le_params (belowB Z) (addBody (belowB X) (wL (diffB X Z))) _ _ N (.allI (.impI ?_)))
  rw [shift_pairT', inst2_addBody]
  exact le_congr (below_pt Z _ _ _).eqSymm (congrAdd (below_pt X _ _ _) (diff_pt X Z _ _ _)).eqSymm
    (below_bit_perturb _ _ _)

/-- `A_z(t) ≤ A_x(t) + R`. -/
theorem above_perturb (N t p : PTm n) : Γ ⊢[PRAAx] le (Ac Z N t p) (Ac X N t p + Rd X Z N p) := by
  refine le_congr (.eqRefl _) ((sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) (diff_sum X Z N t p)))
    (sum_le_params (aboveB Z) (addBody (aboveB X) (wL (diffB X Z))) _ _ N (.allI (.impI ?_)))
  rw [shift_pairT', inst2_addBody]
  exact le_congr (above_pt Z _ _ _).eqSymm (congrAdd (above_pt X _ _ _) (diff_pt X Z _ _ _)).eqSymm
    (above_bit_perturb _ _ _)

/-- The median envelope: if `2(B_x(t) + R) ≤ N` and `2(A_x(t) + R) ≤ N`, then `t` is a balance
median of `z`. -/
theorem robust_median {N t p : PTm n} (h₁ : Γ ⊢[PRAAx] le (two * (Bc X N t p + Rd X Z N p)) N)
    (h₂ : Γ ⊢[PRAAx] le (two * (Ac X N t p + Rd X Z N p)) N) : Γ ⊢[PRAAx] isMed Z N t p :=
  .andI (le_trans (le_mul_mono (le_refl two) (below_perturb X Z N t p)) h₁)
    (le_trans (le_mul_mono (le_refl two) (above_perturb X Z N t p)) h₂)

end Samples

end LeanProofs.IPRA.Probability.MedianRobust
