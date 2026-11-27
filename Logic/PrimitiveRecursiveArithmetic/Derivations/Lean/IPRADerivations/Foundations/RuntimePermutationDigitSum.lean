import IPRADerivations.Foundations.RuntimeWordSorting

/-!
# The sum of numerical permutation digits

The actual adjacent sorting trace preserves the sum of its digits. An
accepted in-range word sorts to the actual identity code, whose digit
sum is the sum of the consecutive positions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationDigitSum

open_ipra exports
open RuntimePermutationWords

variable {n : ℕ} {Γ : List (Fm PTm n)}

def digitTotal (m w : PTm n) : PTm n := ap2 (sumF digitBody) m (data m w)
def positionTotal (m : PTm n) : PTm n := ap2 (sumF (var 0)) m zero

ipra_subst digitTotal

theorem digit_total_congr {m m' w w' : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] digitTotal m w ≐ digitTotal m' w' :=
  congrAp2 _ hm (congrPairT hw hm)

theorem swap_total (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) :
    Γ ⊢[PRAAx] digitTotal m (RuntimeAdjacentPermutationSwap.swapWord m w j) ≐ digitTotal m w := by
  unfold digitTotal
  refine (sum_congr_bounded digitBody (RuntimeAdjacentPermutationSwap.sumSwapBody digitBody)
    (data m (RuntimeAdjacentPermutationSwap.swapWord m w j)) (pairT j (data m w)) m ?_).eqTrans
    (RuntimeAdjacentPermutationSwap.adjacent_sum _ _ _ _ hj)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
  have lo := digit_body_at (Γ := Δ) (Syn.shift m)
    (RuntimeAdjacentPermutationSwap.swapWord (Syn.shift m) (Syn.shift w) (Syn.shift j)) (var 0)
  have swap := RuntimeAdjacentPermutationSwap.swapped_digit (Syn.shift m) (Syn.shift w) (Syn.shift j) (var 0) hjs.wk hi
  have up := (RuntimeAdjacentPermutationSwap.sum_swap_body_at (Γ := Δ) digitBody (Syn.shift j)
      (var 0) (data (Syn.shift m) (Syn.shift w))).eqTrans
    (digit_body_at _ _ (RuntimeAdjacentPermutationSwap.tau (Syn.shift j) (var 0)))
  simpa only [Δ,Syn.shift,subst_data,subst_pairT,RuntimeAdjacentPermutationSwap.subst_swapWord] using
    lo.eqTrans (swap.eqTrans up.eqSymm)

theorem step_total (m w : PTm n) :
    Γ ⊢[PRAAx] digitTotal m (RuntimeWordSorting.sortStep m w) ≐ digitTotal m w := by
  refine .orE (RuntimeWordSorting.active_cases m w) ?_ ?_
  · exact digit_total_congr (.eqRefl _) (RuntimeWordSorting.step_inactive _ _
      (RuntimeWordSorting.inactive_of_active_zero _ _ Prf.hyp0))
  · exact (digit_total_congr (.eqRefl _) (RuntimeWordSorting.step_active _ _ Prf.hyp0)).eqTrans
      (swap_total _ _ _ (.andE₁ (RuntimeWordSorting.descent_found _ _ Prf.hyp0)))

theorem sorting_total (m w t : PTm n) :
    Γ ⊢[PRAAx] digitTotal m (RuntimeWordSorting.state m w t) ≐ digitTotal m w := by
  have all : Γ ⊢[PRAAx] .all
      (digitTotal (Syn.shift m) (RuntimeWordSorting.state (Syn.shift m) (Syn.shift w) (var 0)) ≐
        digitTotal (Syn.shift m) (Syn.shift w)) := by
    ipra_qfind (trivial) [subst_digitTotal, RuntimeWordSorting.subst_state]
    · exact digit_total_congr (.eqRefl _) (RuntimeWordSorting.state_zero _ _)
    · exact (digit_total_congr (.eqRefl _) (RuntimeWordSorting.state_succ _ _ _)).eqTrans
        ((step_total _ _).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,subst_digitTotal,RuntimeWordSorting.subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
    using all.allE t

theorem identity_total (m : PTm n) :
    Γ ⊢[PRAAx] digitTotal m (RuntimeWordSorting.identityCode m) ≐ positionTotal m := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
  have lo := digit_body_at (Γ := Δ) (Syn.shift m) (RuntimeWordSorting.identityCode (Syn.shift m)) (var 0)
  simpa only [Δ,Syn.shift,subst_data,RuntimeWordSorting.subst_identityCode,inst2,Syn.subst_var,
    Matrix.cons_val_zero,ConciseIPRA.PTm.subst_zero] using
    lo.eqTrans (RuntimeWordSorting.identity_code_digit (Syn.shift m) (var 0) hi)

theorem permutation_total (m w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) :
    Γ ⊢[PRAAx] digitTotal m w ≐ positionTotal m :=
  (sorting_total m w (RuntimeWordSorting.fuel m)).eqSymm.eqTrans
    ((digit_total_congr (.eqRefl _) (RuntimeWordSorting.permutation_final_identity _ _ hw hp)).eqTrans
      (identity_total m))

theorem actual_permutation_total_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (var 0)) ⟶ (permutationBit (var 0) (var 1) ≐ one) ⟶
      digitTotal (var 0) (var 1) ≐ positionTotal (var 0)) :=
  closeUniv 2 (.impI (.impI (permutation_total _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimePermutationDigitSum
